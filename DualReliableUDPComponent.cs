using System;
using System.Collections.Generic;
using System.Net;
using System.Net.NetworkInformation;
using System.Net.Sockets;
using System.Text;
using System.Threading;
using UnityEngine;

//连接层功能： 可靠UDP，重传，ACK，序列号回环，消息排序整理，三次握手，主机和客户端一体
//TODO
//1异常处理要完善，
//2大退重登，
//3弱网重连,
//4在一个窗口间隔中，消息未确定，不允许自增，通许也阻塞着，不发送后续的消息
//5超时重传的每条消息要一个 超时时间。
//6握手判定，要和短线重登一起考虑下，接收方避免一直判定列表的ip状态
//7考虑双方都可能一对多，所以每个ip要有一个序列号，各自回环，各自阻塞(根据4)
namespace DualReliableUDP
{
    //连接的目标主机当前状态
    public enum DestinationHostStatus
    {
        SendHand1,
        RecHand1,
        RecHand2,
        SufferConnected,//被连接过来成功了
        ToConnected,//主动连接过去成功了
    }

    public struct MsgPacket
    {
        public IPEndPoint Ip;
        /*
         包格式 
        [0] 8个bit，第一个bit是设置是否handshake，握手包只有第一个byte; 第二个bit是设置是否ACK
        [1 - 8]  handshake = 0 时候，这8个byte是一个序列号，握手包没有序列号；ACK包时候，这个序列号是对方的,ACK包没有数据主体
        剩余的bytes 都是数据主体
         */
        public byte[] Data;
    }

    public class Serialize
    {
        public static bool IsBitSet(byte value, int index)
        {
            if (index < 0 || index >= 8) return false;
            return (value & (1 << index)) != 0;
        }

        public static byte BitSet(byte value, int index)
        {
            if (index < 0 || index >= 8) return value;
            byte mask = (byte)(1 << index);
            return (byte)(value | mask);
        }

        public static byte[] writeULong(ulong value)
        {
            byte[] data = new byte[8];
            for (int i = 0; i < 8; i++)
            {
                data[i] = (byte)((value >> (8 * i)) & 0xFF);
            }
            return data;
        }

        public static ulong readULong(byte[] data)
        {
            int step = -1;
            ulong value = 0UL;
            int pos = 7;
            for (int i = 0; i < 8; i++, pos += step)
            {
                value = (value << 8) | data[pos];//+ data[pos] 也可以
            }
            return value;
        }

        public static byte[] writeUInt(uint value)
        {
            byte[] data = new byte[4];
            for (int i = 0; i < 4; i++)
            {
                data[i] = (byte)((value >> (8 * i)) & 0xFF);
            }
            return data;
        }

        public static uint readUInt(byte[] data)
        {
            int step = -1;
            uint value = 0U;
            int pos = 3;
            for (int i = 0; i < 4; i++, pos += step)
            {
                value = (value << 8) | data[pos];//+ data[pos] 也可以
            }
            return value;
        }

        public static byte[] writeInt(int value)
        {
            byte[] data = new byte[4];
            //将负数转换为32位补码表示
            if (value < 0)
            {
                value = (1 << 32) + value;
            }
            for (int i = 0; i < 4; i++)
            {
                data[i] = (byte)((value >> (8 * i)) & 0xFF);
            }
            return data;
        }

        public static int readInt(byte[] data)
        {
            int step = -1;
            int value = 0;
            int pos = 3;
            for (int i = 0; i < 4; i++, pos += step)
            {
                value = (value << 8) | data[pos];
            }
            //处理负数，如果是负数，取补码
            if (value > (1 << 31))
                value -= (1 << 32);

            return value;
        }
    }

    public class UdpManager
    {
        UdpClient myUDP;// 本机的连接对象，面向多个连接端，可以复用对象

        Thread m_connectThread;//接收线程
        Thread m_sendThread;//发送线程

        public static bool CONNECTION_LOG = true;
        public static bool CONNECTION_HANDSHAKE_LOG = true;

        void LOG(object msg)
        {
            if (CONNECTION_LOG)
            {
                Debug.Log(msg);
            }
        }

        void LOG_HANDSHAKE(object msg)
        {
            if (CONNECTION_HANDSHAKE_LOG)
            {
                Debug.Log(msg);
            }
        }

        //互联网都是这么的理论来的，有一个经验时间来定义一个数据包在网络的流转最大时间
        private ulong sequenceNumber = 0UL;//序列号，有设计回环复用机制就不担心范围溢出问题
        //TODO 每个ip要对应一个序列号

        /*，

           1  [我] 收到 [对方] 发的包   
                     拿出对方的包的序列号，放入 [我收到对方的消息序列号队列]，并且发送一个此序列号的ACK给对方；
                     再次收到此序列号包，丢弃包，并且再次发送一个ACK，因为对方可能没有收到我的确认，从而再次发来
                     直到经验时间过后，我手动移除，等待对方复用，当作下一条新的消息
                     在经验时间过后，理论是对方已经收到我的ACK了，不会再重发，自然会复用这个序列号
           
           2  [我] 发的包 [对方] 已经收到
                     每条发送的消息包，加上我的序列号，然后缓存到 [发送消息队列]，用于检查超时没有收到ACK，自动重发
                     收到这个ACK的序列号，就会移除 [发送消息队列] 对应的序列号消息包，不需要再检查超时重发
                     同时把序列号放到 [[我]发的消息[被][对方]收到后回复的ACK序列号列表]，记录那些序列号被用过，等待复用
                     在列表中的序列号，当再收到这个序列号的ACK，不作处理，丢弃这个ACK包，
                     在经验时间过后，理论是不会再收到这个序列号的ACK包
                     直到这个序列号复用时候，会从这个队列移除，然后复用来作为消息序列号发送，等待下次ACK返回

            3
                在握手成功前，接收方收到的非握手包都丢弃，不回ACK
                握手成功后，双方再收到的握手包，都判定丢弃即可，被动连接的[接收方]还要继续补发hand4
                这样就能保证先握手后再处理通讯消息

            4  大退重登，重新发来握手，主动方与接收方 各自清理掉所有此ip的数据
                主动方更换网络wift->4G，带上token，session发握手，主动方与接收方 也是清理所有playerId或token对应的ip的数据，避免接收方收到属于上一个短连接的同样序列号的数据包
                主动方更换网络wift->4G，没有发来握手，找回token，session对应的ip，更新列表数据为新的 主动方IP
                连接层要提供清理数据，更改目标ip对应数据的接口，方便逻辑层写以上逻辑

            5  弱网重连
                主动方认为要断线重连时候，在发送握手过程收到的消息，都丢弃，因为是上一次连接的消息，直到握手后，再随机新的序列号，继续通讯，避免重复用到上一次连接成功的序列号
        */

        /// <summary>
        /// 目标端的状态，锁，断线重连或大退断开的情况，发送线程才会访问 //接收线程操作，大部分时间主线程不会访问，防止竞争
        /// </summary>
        Dictionary<IPEndPoint, DestinationHostStatus> m_IPEndPointStatus = new();

        /// <summary>
        /// [我]发的消息[被][对方]收到后回复的ACK序列号列表，一个对方ip对应一条列表；序列号是[我]生成的 //接收线程操作锁，发送线程只读不锁
        /// </summary>
        Dictionary<IPEndPoint, List<ulong>> m_recGiveMeACK = new();
        /// <summary>
        /// 我收到对方的消息序列号队列，一个对方ip对应一条队列；序列号是对方生成的 //只是接收线程操作，不用锁
        /// </summary>
        Dictionary<IPEndPoint, List<ulong>> m_recOthersMsg = new();

        /// <summary>
        /// 发送消息队列，锁 //主线程操作
        /// </summary>
        Queue<MsgPacket> m_mainThreadSendMsgQueue = new();
        /// <summary>
        /// 保存发送消息，超时重传，收到 ACK 发送线程中移除 //只是发送线程操作，不用锁
        /// </summary>
        Queue<MsgPacket> m_timeoutSendMsgList = new();
        /// <summary>
        /// 接收线程，数据队列，锁
        /// </summary>
        Queue<MsgPacket> m_recMsgQueue = new();






        //UDP是无顺序保证，需要处理按消息序列号排序后，向逻辑层传送,可以使用TCP窗口模式模拟
        //TODO MsgPacket后续考虑池化，避免太多对象是堆上分配的gc


        //初始化
        public void Init(IPEndPoint ipEnd)
        {
            myUDP = new UdpClient(ipEnd);

            m_connectThread = new Thread(Receive);
            m_connectThread.IsBackground = true;
            m_connectThread.Start();

            m_sendThread = new Thread(Send);
            m_sendThread.IsBackground = true;
            m_sendThread.Start();
        }

        //处理1对1三次握手
        /*
                                       主动方                               接收方

                                    send hand1
                                                                            收到hand1   发送hand2

                     收到hand2  发送hand3 ACK1

                                                                            收到hand3 ACK1    发送hand4 ACK2  （加入列表）
                                                                                                                 (标记是一个被连接过来成功的端)
                   （加入列表） 收到hand4 ACK2 
        标记一个主动连接的端已成功
  



    可靠性    主动方没有收到ACK2 前，表示ACK1 接收方没有收到，超时会继续重发；当收到ACK2 后移除ACK1的重发控制，后续再收到都不处理ACK2
              接收方第一次收到ACK1，处理对应逻辑，放入已经处理的消息队列；后续再收到就丢弃；但是再次收到时候，会再次发送ACK2，因为表示主动方还未收到ACK2
              
         
         */

        //发起握手
        public void BeginHandShake(IPEndPoint ip)
        {
            lock (m_IPEndPointStatus)
            {
                bool matchIP = m_IPEndPointStatus.TryGetValue(ip, out DestinationHostStatus status);

                //判定还未连接上，是hand1阶段才发
                if (!matchIP)
                {
                    LOG_HANDSHAKE("主动方马上发送握手 hand1" + $": 对方IP {ip}");
                    m_IPEndPointStatus[ip] = DestinationHostStatus.SendHand1;
                    MsgPacket pack = getHandPack(ip);
                    blockSend(pack);
                }
            }
        }

        //发送消息
        public void SendTo(IPEndPoint ip, byte[] data)
        {
            MsgPacket pack = createMsg(ip, data);
            lock (this.m_mainThreadSendMsgQueue)
            {
                m_mainThreadSendMsgQueue.Enqueue(pack);
            }
        }

        //填充已经收到的消息给外部队列
        public void FillMsg(ref Queue<MsgPacket> outQueue)
        {
            lock (m_recMsgQueue)
            {
                while (m_recMsgQueue.Count > 0)
                {
                    outQueue.Enqueue(m_recMsgQueue.Dequeue());
                }
            }
        }

        //填充最新的目标IP状态
        public void FillIpStatus(ref Dictionary<IPEndPoint, DestinationHostStatus> curStatus)
        {
            try
            {
                if (m_IPEndPointStatus.Count > 0)
                {
                    foreach (var kv in m_IPEndPointStatus)
                    {
                        curStatus.Add(kv.Key, kv.Value);
                    }
                }
            }
            catch (Exception ex)
            {
                Debug.LogError("FillIpStatus copy m_IPEndPointStatus exception: " + ex.Message);
            }
        }

        public void Close()
        {
            if (m_connectThread != null && m_connectThread.IsAlive)
            {
                m_connectThread.Abort();
                m_connectThread = null;
            }
            if (m_sendThread != null && m_sendThread.IsAlive)
            {
                m_sendThread.Abort();
                m_sendThread = null;
            }
            if (myUDP != null)
            {
                myUDP.Close();
                myUDP.Dispose();
                myUDP = null;
                LOG("销毁连接层");
            }
        }

        MsgPacket getHandPack(IPEndPoint ip)
        {
            //握手包标记位
            int handshakeBitIndex = 1;
            byte nonHand = 0;
            byte handBit = Serialize.BitSet(nonHand, handshakeBitIndex - 1);
            byte[] data = new byte[1];
            data[0] = handBit;
            MsgPacket pack;
            pack.Ip = ip;
            pack.Data = data;

            return pack;
        }

        void blockSend(MsgPacket pack)
        {
            try
            {
                myUDP.Send(pack.Data, pack.Data.Length, pack.Ip);
            }
            catch (System.Exception ex)
            {
                Debug.LogError("Block send exception:" + ex.Message);
            }
        }

        DateTime handshakeTimeOut = DateTime.Now;
        double handshakeTimeOutReset = 300D;

        void sendHandShake3()
        {
            //控制握手包重发频率，暂时所有ip在同一个时间频率下重发，后续考虑每个ip一个时间值
            //TODO要研究怎么控制重发超时的时间设置，不然会错误重复的重发
            double elapsed = (DateTime.Now - handshakeTimeOut).TotalMilliseconds;
            if (elapsed > handshakeTimeOutReset)
            {
                handshakeTimeOut = DateTime.Now;
            }
            else
            {
                return;
            }

            Dictionary<IPEndPoint, DestinationHostStatus> curStatus = new();
            //lock (m_IPEndPointStatus)//发送线程调用，只读不写，不锁，避免竞争无法收发同步，因为重发检查时候，状态滞后一点，多发一些也没问题的
            FillIpStatus(ref curStatus);

            var ks = curStatus.Keys;
            foreach (var ip in ks)
            {
                var status = curStatus[ip];
                MsgPacket pack = new MsgPacket();

                if (status == DestinationHostStatus.SendHand1)
                {
                    LOG_HANDSHAKE("主动方发了hand1， 还未收到hand2，定时重发 hand1" + $": 对方IP {ip}");
                    pack = getHandPack(ip);
                }
                else if (status == DestinationHostStatus.RecHand1)
                {
                    LOG_HANDSHAKE("接收方收到hand1， 还未收到hand3，定时重发 hand2" + $": 对方IP {ip}");
                    pack = getHandPack(ip);
                }
                else if (status == DestinationHostStatus.RecHand2)
                {
                    LOG_HANDSHAKE("主动方收到hand2，还未收到hand4，定时重发hand3" + $": 对方IP {ip}");
                    pack = getHandPack(ip);
                }
                if (pack.Data != null && pack.Data.Length > 0)
                {
                    LOG_HANDSHAKE("<color=blue>定时检查，超时重发的握手包" + $": 对方IP {ip}</color>");
                    blockSend(pack);
                }
            }
        }

        bool recHandShake3(MsgPacket handPak)
        {
            //判定是否握手包标记位
            int handshakeBitIndex = 1;
            bool handshake = Serialize.IsBitSet(handPak.Data[0], handshakeBitIndex - 1);

            lock (m_IPEndPointStatus)
            {
                var matchIP = m_IPEndPointStatus.TryGetValue(handPak.Ip, out DestinationHostStatus status);
                //Debug.Log($"matchIP {matchIP} ,  status {status.ToString()}");
                //检查是主动连接成功，还是被动连接成功
                bool isToConnect = matchIP && status == DestinationHostStatus.ToConnected;//主动连接是否成功
                bool isSufferConnected = matchIP && status == DestinationHostStatus.SufferConnected;//被连接过来的成功
                MsgPacket pack = new MsgPacket();

                //这里的判定目的是: 被动接收方 成功就不用看主动方，避免双方都是调用这个代码，产生误判
                if (!isSufferConnected)
                {
                    if (!isToConnect)
                    {
                        if (!handshake)
                        {
                            //还在握手的过程，收到非握手包，都丢弃，返回正在握手阶段
                            LOG_HANDSHAKE("[主动方 发起连接] 或 [被动接收方 被发起的连接] 未成功\n还在握手的过程，收到非握手包，都丢弃" + $": 对方IP {handPak.Ip}");
                            //这个时候收到非握手包，就是消息包，都丢弃也没问题，对方如果是先握手成功，发起的消息包，没收到我的ACK，对方会继续超时重发，不会丢掉
                            return true;
                        }
                    }
                }//

                if (isToConnect && handshake)
                {
                    LOG_HANDSHAKE("主动方发起连接已成功 不是握手过程，又收到握手包 hand4，也丢弃，返回正在握手阶段" + $": 对方IP {handPak.Ip}");
                    return true;
                }
                if (isSufferConnected && handshake)
                {
                    //3 被动连接方 被发起的连接已成功 不是握手过程，又收到握手包，也丢弃，返回正在握手阶段
                    LOG_HANDSHAKE("接收方还要继续补发hand4，可能发起连接方 未收到hand4，再发来了hand3" + $": 对方IP {handPak.Ip}");
                    pack = getHandPack(handPak.Ip);
                }

                if (!handshake) return false;

                if (!matchIP)
                {
                    //接收到一个未连接的ip过来，
                    LOG_HANDSHAKE("接收方 收到了 hand1，马上发送hand2" + $": 对方IP {handPak.Ip}");
                    m_IPEndPointStatus[handPak.Ip] = DestinationHostStatus.RecHand1;
                    pack = getHandPack(handPak.Ip);
                }
                else
                {
                    if (status == DestinationHostStatus.SendHand1)
                    {
                        LOG_HANDSHAKE("主动方发了hand1，收到了 hand2， 马上发送hand3");
                        m_IPEndPointStatus[handPak.Ip] = DestinationHostStatus.RecHand2;
                        pack = getHandPack(handPak.Ip);
                    }
                    else if (status == DestinationHostStatus.RecHand1)
                    {
                        LOG_HANDSHAKE("接收方是收过了hand1， 收到hand3， 马上发送hand4， <color=green>[标记被动连接成功]" + $": 对方IP {handPak.Ip}</color>");
                        m_IPEndPointStatus[handPak.Ip] = DestinationHostStatus.SufferConnected;
                        pack = getHandPack(handPak.Ip);
                    }
                    else if (status == DestinationHostStatus.RecHand2)
                    {
                        LOG_HANDSHAKE("主动方是收过hand2， 收到hand4， <color=green>[标记主动连接成功]" + $": 目标IP {handPak.Ip}</color>");
                        m_IPEndPointStatus[handPak.Ip] = DestinationHostStatus.ToConnected;
                        return true; //最后一个握手包，所以也返回正在握手阶段
                    }
                }
                if (pack.Data != null && pack.Data.Length > 0)
                {
                    //LOG_HANDSHAKE("收到握手包时候，回送握手包" + $": 对方IP {handPak.Ip}");
                    blockSend(pack);
                    return true;
                }
            }
            return false;
        }

        void Send()
        {
            Queue<MsgPacket> sending = new();
            while (true)
            {
                //TODO 考虑主动方连接成功后，不用继续检查握手；要和断线重连和大退重连一起考虑
                sendHandShake3();

                //发送不用考虑此ip是否握手成功，因为接收时候判定了会丢弃，不回ACK，这样超时重发即可
                if (m_mainThreadSendMsgQueue.Count == 0 && m_timeoutSendMsgList.Count == 0)
                {
                    Thread.Sleep(1);
                    continue;
                }
                sending.Clear();
                lock (this.m_mainThreadSendMsgQueue)
                {
                    while (this.m_mainThreadSendMsgQueue.Count > 0)
                    {
                        sending.Enqueue(m_mainThreadSendMsgQueue.Dequeue());
                    }
                }


                while (sending.Count > 0)
                {
                    var pack = sending.Dequeue();
                    //放入超时重传队列
                    m_timeoutSendMsgList.Enqueue(pack);

                    blockSend(pack);
                }
                //检查超时重传
                timeoutResend();
            }
        }

        void Receive()
        {
            while (true)
            {
                try
                {
                    IPEndPoint ipEndPoint = null;
                    MsgPacket packet;
                    var data = myUDP.Receive(ref ipEndPoint);
                    if (ipEndPoint != null)
                    {
                        packet.Ip = ipEndPoint;
                        packet.Data = data;

                        //TODO 考虑主动方连接成功后，不用继续检查握手；要和断线重连和大退重连一起考虑
                        if (recHandShake3(packet)) continue;

                        //ACK和通讯消息分开处理
                        if (recGiveMeACK(packet)) continue;
                        recMsg(packet);
                    }
                    else
                    {
                        Debug.LogError("Receive exception : ipEndPoint null");
                    }
                }
                catch (System.Exception ex)
                {

                    Debug.LogError("Receive exception :" + ex.Message);

                }
            }
        }

        DateTime sendMsgTimeOut = DateTime.Now;
        double sendMsgTimeOutReset = 500D;

        void timeoutResend()
        {
            double elapsed = (DateTime.Now - sendMsgTimeOut).TotalMilliseconds;
            if (elapsed > sendMsgTimeOutReset)
            {
                sendMsgTimeOut = DateTime.Now;
                //超时重发
            }
            else
            {
                return;
            }

            //拷贝，只读不锁，避免阻塞, 因为重发检查时候，数据滞后一点，多发一些也没问题的
            Dictionary<IPEndPoint, List<ulong>> allGiveMeACK = new();
            try
            {
                if (m_recGiveMeACK.Count > 0)
                {
                    foreach (var kv in m_recGiveMeACK)
                    {
                        allGiveMeACK.Add(kv.Key, kv.Value);
                    }
                }
            }
            catch (Exception ex)
            {
                Debug.LogError("timeoutResend copy m_recGiveMeACK exception :" + ex.Message);
            }

            //先检查一遍，哪些已经收到了ACK，收到过了的消息，就移除不用重发  注意整理数据要避免GC
            int count = m_timeoutSendMsgList.Count;
            var temp = new Queue<MsgPacket>();

            for (int i = 0; i < count; i++)
            {
                var pack = m_timeoutSendMsgList.Dequeue();
                ulong mySeq = getDataSeq(pack.Data);
                bool recIPACK = allGiveMeACK.TryGetValue(pack.Ip, out List<ulong> seqs);//是否已经收到过这个IP会给我的ACK
                bool isRecACK = recIPACK && seqs.Contains(mySeq);//有收到这个IP，并且有存在这个序列号在列表
                //还未收到，超时判定，重发，然后放回列表等待下次检查
                if (!isRecACK)
                {
                    LOG($"<color=blue>还未收到此ip给我的ACK ,重发一个Pack => ip: {pack.Ip} , mySeq: {mySeq}</color>");
                    blockSend(pack);
                    temp.Enqueue(pack);
                }
            }
            for (int i = 0; i < temp.Count; i++)
            {
                m_timeoutSendMsgList.Enqueue(temp.Dequeue());
            }
        }

        //处理 [我] 发的包 [对方] 已经收到
        bool recGiveMeACK(MsgPacket pak)
        {
            //是否ACK标记
            int ackBitIndex = 2;
            bool isACK = Serialize.IsBitSet(pak.Data[0], ackBitIndex - 1);
            if (isACK)
            {
                lock (m_recGiveMeACK)
                {
                    bool recIPACK = m_recGiveMeACK.TryGetValue(pak.Ip, out List<ulong> seqs);
                    if (!recIPACK)
                    {
                        //第一次收到这个ip 回给我的ACK
                        seqs = new List<ulong>();
                        m_recGiveMeACK.Add(pak.Ip, seqs);
                    }
                    //检查是否存在这个对方 回给我的ACK
                    ulong mySeq = getDataSeq(pak.Data);
                    bool reced = seqs.Contains(mySeq);
                    if (!reced)
                    {
                        //没有收过，加入队列
                        seqs.Add(mySeq);
                        m_recGiveMeACK[pak.Ip] = seqs;//更新防止值传递

                        LOG($"我 收到 对方给我的ACK: ip {pak.Ip} , seq {mySeq}");
                    }
                    else
                    {
                        //，有的证明已经收过，丢弃这个包，不处理
                        LOG($"我 !!!重复!!!  收到 对方给我的相同序列号ACK 丢弃： ip {pak.Ip} , seq {mySeq}");
                    }
                }
            }

            return isACK;
        }

        //处理 [我] 收到 [对方] 发给我的包
        void recMsg(MsgPacket pak)
        {
            bool recIPed = m_recOthersMsg.TryGetValue(pak.Ip, out List<ulong> seqs);
            if (!recIPed)
            {
                //第一次收到这个ip的消息
                seqs = new List<ulong>();
                m_recOthersMsg.Add(pak.Ip, seqs);
            }
            //拿出对方序列号，给对方发一个ACK
            ulong otherSeq = getDataSeq(pak.Data);

            //检查是否存在这个对方给过来的消息序列号
            bool reced = seqs.Contains(otherSeq);
            if (!reced)
            {
                //没有收过，加入队列
                seqs.Add(otherSeq);
                m_recOthersMsg[pak.Ip] = seqs;//更新防止值传递

                LOG($"我收到此ip 发给我的消息: ip {pak.Ip}, seq {otherSeq}");

                //TODO 处理消息顺序窗口
                lock (m_recMsgQueue)
                {
                    //开始放入接收数据队列
                    m_recMsgQueue.Enqueue(pak);
                }
            }
            else
            {
                LOG($"我!!!重复!!! 收到此ip 发给我的相同序列号消息,  丢弃: ip {pak.Ip}, seq {otherSeq}");
                //，有的证明已经收过，丢弃这个包
            }

            MsgPacket ackPak = createACK(pak.Ip, otherSeq);
            LOG($"我给 对方 一个ACK : 对方ip {pak.Ip}, 对方序列号 {otherSeq}");
            blockSend(ackPak);
        }

        //反序列化序列号
        ulong getDataSeq(byte[] data)
        {
            byte[] seqBs = new byte[8];
            Buffer.BlockCopy(data, 1, seqBs, 0, 8);
            ulong seq = Serialize.readULong(seqBs);
            return seq;
        }

        byte[] getMsgHeadData(ulong sequence, bool isACK)
        {
            int ackBitIndex = 2;
            byte ack = 0;
            if (isACK) ack = Serialize.BitSet(ack, ackBitIndex - 1);
            byte[] senderSequenceData = Serialize.writeULong(sequence);
            byte[] data = new byte[9];//1-8 ulong序列号
            data[0] = ack;
            Buffer.BlockCopy(senderSequenceData, 0, data, 1, senderSequenceData.Length);
            return data;
        }

        //senderSequence 对方的序列号
        MsgPacket createACK(IPEndPoint ip, ulong senderSequence)
        {
            //用发送方的序列号，放入ACK包，回复给发送方
            byte[] data = getMsgHeadData(senderSequence, true);

            MsgPacket pack;
            pack.Ip = ip;
            pack.Data = data;
            return pack;
        }

        MsgPacket createMsg(IPEndPoint ip, byte[] msgBody)
        {
            //发送消息，先获得我当前序列号
            ulong mySequence = GetSequence();
            LOG($"我 主动发的消息: 对方IP {ip}, 这条消息我的序列号 {mySequence}");
            byte[] headData = getMsgHeadData(mySequence, false);
            int headLen = headData.Length;
            int bodylen = msgBody.Length;
            byte[] data = new byte[headData.Length + bodylen];
            Buffer.BlockCopy(headData, 0, data, 0, headLen);
            Buffer.BlockCopy(msgBody, 0, data, headLen, bodylen);
            MsgPacket pack;
            pack.Ip = ip;
            pack.Data = data;
            return pack;
        }











        ulong GetSequence()
        {
            return sequenceNumber++;//TEMP
        }

        //经验时间过后，移除列表中的回收序列号，暂时定 2分钟，将前面的序列号回收
        /*
         回收策略
         */
        void RecoverSequence()
        {

        }




        //处理重登，重连的连接逻辑
        void HandleRelogin()
        {

        }


    }

    /////////////////////////////////////////////////逻辑层/////////////////////////////////////
    public class UDPManagerLogic : MonoBehaviour
    {
        //处理流水线，大退重登，断线重连，序列化，拦截，数据加工, RPC包处理，等逻辑
        //监听服务器：主机和客户端一体时，本机不用连接，调用逻辑层时候，直接回传到业务层；
        //本机客户端发送到本主机的消息包，不用传递到连接层，直接放入本主机的接收队列，模拟有消息发过来
        //本主机广播给本机客户端的消息包，不用传递到连接层，直接放入本机客户端的接收队列，模拟有消息下发
        //主机的逻辑层广播给其他连接过来的主动方

        //适应业务层，状态同步，帧同步都可以

        public bool ListenServer = false;//监听服务器
        public bool DedicateServer = false;//独立服务器
        public bool Client = false;//只是客户端

        //RPC调用，发送和接收都是函数名，主机和客户端一体也能调用，无需分主机和客户端的消息接收队列

        //RPC调用：要判定业务层发送的消息包，是广播还是单端发送，主机可以调用单端或者多端，看业务层逻辑怎么决定

        //主线程拷贝接收线程缓存队列的数据，控制拷贝频率，防止竞争
        Queue<MsgPacket> m_mainThreadRecMsgQueue = new();
        //给到业务层的消息包，要去掉包头后的msg body

        //逻辑层定时获得连接层的ip状态，提供给业务层判定，UI显示连接图片，业务在接收方检查对方是否连接上，能不能给他广播
        Dictionary<IPEndPoint, DestinationHostStatus> curStatus = new();
        float curStatusUpdateStep = 1000f;//1秒

        //连接层对象
        DualReliableUDP.UdpManager mgr;

        public void ServerTravel(string sceneName, string ip = "", int port = 0, bool isListenServer = false)
        {
            //监听服务器或独立服务器，服务端启动后，进入选定的场景，等待其他客户端进入
            //进入的场景会通过RPC ，被客户端调用ClientTravel时候，返回场景名，让客户端连接后，自动切换到场景
            //类似CS，主机开启了地图，在地图中等待其他客户端进入，进入后发现正在对局，就等待下一局，这个是游戏玩法决定；
            //可以等待所以客户端进入，服务端再广播战斗开始，此期间客户端都不能移动，只能做其他动画之类

            //isListenServer 传入监听服务器标记，就开启监听模式
            ListenServer = isListenServer;
            DedicateServer = !isListenServer;
            IPEndPoint iPEnd = new IPEndPoint(IPAddress.Parse(ip), port);
            mgr.Init(iPEnd);

            //服务端切换场景，缓存场景名
        }

        public void ClientTravel(string ip, int port)
        {
            //RPC调用服务端的连接接口，获得服务端场景名，同时连接ip端口，连接成功后，主动切换场景名
            //服务端业务层，发现客户端进入，会广播给客户端信息，进行同步
            Client = true;
            IPEndPoint ipEnd = new IPEndPoint(IPAddress.Any, 0);
            mgr.Init(ipEnd);

            //开始连接服务端
            //TODO 判定这个ip，我是否已经握手成功，连接上；未连接不能发消息，要判定连接端的状态

            //切换场景后，RPC调用给服务端PostLogin，让其知道客户端切换完毕，准备好了
            //服务端回一个RPC，让客户端创建角色，分配一个player

        }

        //客户端连接成功，切换场景后，RPC调用此函数，传递有一个客户端进入到服务端；
        //此函数在服务端调用
        //[SERVER]
        void PostLogin()
        {

        }

        //TODO客户端主动断开连接，主动调用或者连接层检测断开调用(与断线重连大退重登有关)
        //[SERVER]
        void Logout()
        {

        }

        private void OnDestroy()
        {
            mgr.Close();
            mgr = null;
        }

        private void Start()
        {
            mgr = new DualReliableUDP.UdpManager();
        }

        private void Update()
        {
            //主线程要判定连接端的状态 所以update 固定频率下把m_IPEndPointStatus 拷贝到主线程更新连接端状态，防止持续lock，接收线程。
            //可以考虑不lock，读不互斥






            //update到接收线程拿数据
            //mgr.FillMsg(ref m_mainThreadRecMsgQueue);


            ////派发业务层
            //int count = 0;
            //while (m_mainThreadRecMsgQueue.Count > 0)
            //{
            //    m_mainThreadRecMsgQueue.Dequeue();

            //    //每一帧至多处理N个消息，避免消息处理主线程卡帧
            //    if (++count >= 100)
            //    {
            //        break;
            //    }
            //}
        }
    }




    /// ///////////////////////////////////////////////封装组件层//////////////////////////////////////////////////


    public class DualReliableUDPComponent : MonoBehaviour
    {
        public bool DedicateServer = false;//独立服务器
        public bool DedicateServerAutoIP = true;
        public int ServerPort = 80088;
        public string ServerIp = "127.0.0.1";

        DualReliableUDP.UdpManager mgr;

        //ulong _playerIDPool = 0UL;//分配一个playerId
        //Dictionary<IPEndPoint, ulong> m_clientIPEndPointPlayerId = new();//客户端的PlayerId 与 ip映射，记录已经连接上来的客户端
        //Dictionary<ulong, IPEndPoint> m_clientIPEndPointPlayerIdR = new();//双向


        // Start is called before the first frame update
        void Start()
        {
            //服务端的初始化ip
            //IPEndPoint ipEnd = new IPEndPoint(IPAddress.Parse(DualReliableUDP.SocketDefine.ip), DualReliableUDP.SocketDefine.port);//服务器，开放自己的ip和端口
            //客户端的初始化ip
            //IPEndPoint ipEnd = new IPEndPoint(IPAddress.Any, 0);//!!!!! 这创建客户端的链接对象，必须端口0，表示这是客户端，准备连接服务器的，不是服务器，开放自己的ip和端口


            if (DedicateServerAutoIP)
            {
                //unity当前进程端口号，作为服务器UDP连接打开端口
                int port = System.Diagnostics.Process.GetCurrentProcess().Id;
                ServerPort = port;

                string ip = GetIP();
                ServerIp = ip;
            }
            mgr = new DualReliableUDP.UdpManager();

            if (DedicateServer)
            {
                //先启动 服务器，打印端口号，ip地址，给客户端填写
                Debug.Log("服务器当前进程端口号 :" + ServerPort.ToString());
                Debug.Log("服务器当前OS的ip地址 :" + ServerIp);

                //服务端的初始化ip
                IPEndPoint ipEnd = new IPEndPoint(IPAddress.Parse(ServerIp), ServerPort);//服务器，开放自己的ip和端口

                mgr.Init(ipEnd);
            }
            else
            {
                //客户端的初始化ip
                IPEndPoint ipEnd = new IPEndPoint(IPAddress.Any, 0);//!!!!! 这创建客户端的链接对象，必须端口0，表示这是客户端，准备连接服务器的，不是服务器，开放自己的ip和端口
                mgr.Init(ipEnd);
            }
        }

        private void OnGUI()
        {
            //客户端有按钮，开始主动发送后，服务端才可以定时回信息
            if (!DedicateServer)
            {
                var buttonWidth = 300;
                var buttonHeight = 300;

                var buttonX = (Screen.width - buttonWidth) / 2.0f;
                var buttonY = (Screen.height - buttonHeight) / 2.0f;
                IPEndPoint ipEnd = new IPEndPoint(IPAddress.Parse(ServerIp), ServerPort);//服务器，开放自己的ip和端口

                if (GUI.Button(new Rect(buttonX, buttonY, buttonWidth, buttonHeight), "连接服务器"))
                {
                    mgr.BeginHandShake(ipEnd);
                }

                if (GUI.Button(new Rect(buttonX, buttonY + 350, buttonWidth, buttonHeight), "发送消息"))
                {
                    byte[] data = Encoding.UTF8.GetBytes("发88888888");
                    mgr.SendTo(ipEnd, data);
                }
            }
        }

        private void OnDestroy()
        {

            mgr.Close();

        }

        // Update is called once per frame
        void Update()
        {

            Queue<MsgPacket> m_mainThreadRecMsgQueue = new Queue<MsgPacket>();
            mgr.FillMsg(ref m_mainThreadRecMsgQueue);


            //派发业务层
            int count = 0;
            while (m_mainThreadRecMsgQueue.Count > 0)
            {
                var msg = m_mainThreadRecMsgQueue.Dequeue();
                byte[] msgBody = new byte[msg.Data.Length - 9];
                Buffer.BlockCopy(msg.Data, 9, msgBody, 0, msg.Data.Length - 9);
                string msgStr = Encoding.UTF8.GetString(msgBody);
                if (DedicateServer)
                {
                    Debug.Log($"服务器收到一个消息 : 客户端ip {msg.Ip}, 内容 {msgStr}");

                    string sendmsg = "收88888888";
                    byte[] sendData = Encoding.UTF8.GetBytes(sendmsg);
                    mgr.SendTo(msg.Ip, sendData);
                }
                else
                {
                    Debug.Log($"客户端收到服务器发来一个消息 : 服务器ip {msg.Ip}, 内容 {msgStr}");
                }
                //每一帧至多处理N个消息，避免消息处理主线程卡帧
                if (++count >= 100)
                {
                    break;
                }
            }
        }



        /// <summary>
        /// 获取本机IP
        /// </summary>
        /// <returns>string :ip地址</returns>
        string GetIP()
        {
            NetworkInterface[] adapters = NetworkInterface.GetAllNetworkInterfaces();
            foreach (NetworkInterface adater in adapters)
            {
                if (adater.Supports(NetworkInterfaceComponent.IPv4))
                {
                    UnicastIPAddressInformationCollection UniCast = adater.GetIPProperties().UnicastAddresses;
                    if (UniCast.Count > 0)
                    {
                        foreach (UnicastIPAddressInformation uni in UniCast)
                        {
                            if (uni.Address.AddressFamily == AddressFamily.InterNetwork)
                            {
                                //Debug.Log(uni.Address.ToString());
                                return uni.Address.ToString();
                            }
                        }
                    }
                }
            }
            return null;
        }

        string GetLocalIP()
        {
            try
            {
                IPHostEntry IpEntry = Dns.GetHostEntry(Dns.GetHostName());
                foreach (IPAddress item in IpEntry.AddressList)
                {
                    //AddressFamily.InterNetwork  ipv4
                    //AddressFamily.InterNetworkV6 ipv6
                    if (item.AddressFamily == AddressFamily.InterNetwork)
                    {
                        return item.ToString();
                    }
                }
                return "";
            }
            catch { return ""; }
        }
    }
}
