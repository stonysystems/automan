﻿namespace IronRSLClient
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Net;
    using System.Runtime.InteropServices;
    using System.Threading;
    using System.Linq;
    using System.Threading.Tasks;
    using System.Diagnostics;
    using System.Text;
    using System.Security.Cryptography;
    using Newtonsoft.Json;
    
    public class HiResTimer
    {
        private static Stopwatch _stopWatch = null;
        public static long Ticks
        {
            get
            {
                return _stopWatch.ElapsedTicks;
            }
        }
        public static void Initialize()
        {
            _stopWatch = Stopwatch.StartNew();
        }
        public static double TicksToMilliseconds(long ticks)
        {
            return ticks * 1000.0 / Stopwatch.Frequency;
            return ticks * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3);
        }

    }

    public struct Param
    {
        public int id;
        public int port_num;
        public ulong initial_seq_no;
        public int []num_req_cnt_a;
        public double []latency_cnt_ms_a;
        public string keyFilePath;
    }

    public abstract class ClientBase
    {
        protected System.Net.Sockets.UdpClient udpClient;

        public static List<IPEndPoint> endpoints;
        public static IPAddress my_addr;

        private readonly Dictionary<string, byte[]> nodeKeys = new Dictionary<string, byte[]>();
        

        public static uint encodedClientAddress()
        {
            //byte[] asbytes = new byte[] { 172, 31, 24, 152 };
            byte[] asbytes = my_addr.GetAddressBytes();
            return ExtractBE32(asbytes, 0);
        }

        public static void StartThread(object p)
        {
            Thread.Sleep(3000);
            var param = (Param)p;
            var c = new Client(param.keyFilePath); // 使用 keyFilePath 创建 Client 实例
            c.Main(param.id, param.port_num, param.initial_seq_no, param.num_req_cnt_a, param.latency_cnt_ms_a);
        }


        static public IEnumerable<Thread> StartThreads<T>(
            int num_threads, 
            int port_num, 
            ulong initial_seq_no, 
            int []num_req_cnt_a_, 
            double []latency_cnt_ms_a_,
            string keyFilePath
        ) where T : ClientBase//, new()
        {
            if (num_threads < 0)
            {
                throw new ArgumentException("number of threads is less than 1", "num_threads");
            }

            for (int i = 0; i < num_threads; ++i)
            {
                var t = new Thread(StartThread);
                var param = new Param
                {
                    id = i,
                    port_num = port_num,
                    initial_seq_no = initial_seq_no,
                    num_req_cnt_a = num_req_cnt_a_,
                    latency_cnt_ms_a = latency_cnt_ms_a_,
                    keyFilePath = keyFilePath // 传递 keyFilePath
                };
                t.Start(param);
                yield return t;

                // // var t = new Thread(StartThread);
                // var t = new Thread(() =>
                // {
                //     var client = (T)Activator.CreateInstance(typeof(T), keyFilePath);
                //     client.Main(i, port_num, initial_seq_no, num_req_cnt_a_, latency_cnt_ms_a_);
                // });
                // t.Start();

                // var p = new Param { id = i, port_num = port_num, initial_seq_no = initial_seq_no, num_req_cnt_a = num_req_cnt_a_, latency_cnt_ms_a = latency_cnt_ms_a_ };
                // t.Start(p);
                yield return t;
            }
        }

        public ClientBase(string keyFilePath)
        {
            LoadKeysFromFile(keyFilePath);
        }

        private void LoadKeysFromFile(string filePath)
        {
            if (!File.Exists(filePath))
            {
                throw new FileNotFoundException($"Key file not found: {filePath}");
            }

            string json = File.ReadAllText(filePath);
            var keys = JsonConvert.DeserializeObject<Dictionary<string, string>>(json);

            foreach (var pair in keys)
            {
                nodeKeys[pair.Key] = Encoding.UTF8.GetBytes(pair.Value);
            }

            // Console.WriteLine("Keys loaded successfully.");
        }

        protected byte[] GetKeyForEndpoint(IPEndPoint remote)
        {
            string address = remote.Address.ToString();
            if (nodeKeys.ContainsKey(address))
            {
                return nodeKeys[address];
            }

            throw new InvalidOperationException($"No key found for endpoint {address}");
        }


        protected abstract void Main(int id, int port_num, ulong initial_seq_no, int []num_req_cnt_a_, double []latency_cnt_ms_a_);

        protected void Send(MessageBase msg, System.Net.IPEndPoint remote)
        {
            byte[] key = GetKeyForEndpoint(remote);
            byte[] messageWithHmac = msg.ToByteArrayWithHmac(key);

            if (this.udpClient.Send(messageWithHmac, messageWithHmac.Length, remote) != messageWithHmac.Length)
            {
                throw new InvalidOperationException("Failed to send complete message.");
            }

            // var a = msg.ToBigEndianByteArray();
            // if (this.udpClient.Send(a, a.Length, remote) != a.Length)
            // {
            //     throw new InvalidOperationException("failed to send complete message.");
            // }
        }

        protected byte[] Receive()
        {
            IPEndPoint remote = null;
            byte[] receivedMessage = this.udpClient.Receive(ref remote);

            // ParseMessage(receivedMessage, out byte[] receivedHmac, out byte[] messageContent);
            MessageBase.ParseMessage(receivedMessage, out byte[] hmac, out byte[] messageContent);

            return messageContent;
        }

        // protected byte[] Receive()
        // {
        //     IPEndPoint remote = null;
        //     byte[] receivedMessage = this.udpClient.Receive(ref remote);

        //     byte[] key = GetKeyForEndpoint(remote);
        //     if (!MessageBase.VerifyHmac(receivedMessage, key, out byte[] messageContent))
        //     {
        //         throw new InvalidOperationException("HMAC verification failed for received message.");
        //     }

        //     return messageContent;

        //     // IPEndPoint endpoint = null;
        //     // return this.udpClient.Receive(ref endpoint);          
        // }

        public ulong MyAddress64()
        {
            System.Net.IPEndPoint ep = (System.Net.IPEndPoint) udpClient.Client.LocalEndPoint;
            ushort port = (ushort) ep.Port;
            uint addr = encodedClientAddress();
            MemoryStream str = new MemoryStream();
            ushort preamble = 0;
            var bytes = BitConverter.GetBytes(preamble);
            str.Write(bytes, 0, bytes.Length);
            bytes = BitConverter.GetBytes(addr);
            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            str.Write(bytes, 0, bytes.Length);
            bytes = BitConverter.GetBytes(port);
            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            str.Write(bytes, 0, bytes.Length);
            byte[] s = str.ToArray();
            Array.Reverse(s);
            return BitConverter.ToUInt64(s, 0);
        }

        public static UInt64 ExtractBE64(byte[] byteArray, int offset)
        {
            byte[] extractedBytes = byteArray.Skip(offset).Take(8).ToArray();
            Array.Reverse(extractedBytes);
            return BitConverter.ToUInt64(extractedBytes, 0);
        }
        public static UInt32 ExtractBE32(byte[] byteArray, int offset)
        {
            byte[] extractedBytes = byteArray.Skip(offset).Take(4).ToArray();
            Array.Reverse(extractedBytes);
            return BitConverter.ToUInt32(extractedBytes, 0);
        }
    }

    public abstract class MessageBase
    {
        public ulong CaseId { get; private set; }

        protected MessageBase(ulong caseId)
        {
            this.CaseId = caseId;
        }

        public abstract byte[] ToBigEndianByteArray();

        public byte[] ToByteArrayWithHmac(byte[] key)
        {
            byte[] message = this.ToBigEndianByteArray();
            byte[] hmac = GenerateHmac(message, key);

            // Combine HMAC and message
            byte[] fullMessage = new byte[hmac.Length + message.Length];
            Buffer.BlockCopy(hmac, 0, fullMessage, 0, hmac.Length);
            Buffer.BlockCopy(message, 0, fullMessage, hmac.Length, message.Length);

            return fullMessage;
        }

        public static bool VerifyHmac(byte[] receivedMessage, byte[] key, out byte[] messageContent)
        {
            int hmacLength = 32; // Length of HMAC-SHA256
            if (receivedMessage.Length < hmacLength)
            {
                messageContent = null;
                return false;
            }

            // Extract HMAC and message
            byte[] receivedHmac = new byte[hmacLength];
            messageContent = new byte[receivedMessage.Length - hmacLength];
            Buffer.BlockCopy(receivedMessage, 0, receivedHmac, 0, hmacLength);
            Buffer.BlockCopy(receivedMessage, hmacLength, messageContent, 0, messageContent.Length);

            // Compute HMAC of the message content
            byte[] computedHmac = GenerateHmac(messageContent, key);
            return SlowEquals(computedHmac, receivedHmac);
        }

        public static void ParseMessage(byte[] receivedMessage, out byte[] hmac, out byte[] messageContent)
        {
            int hmacLength = 32;
            if (receivedMessage.Length < hmacLength)
            {
                throw new ArgumentException("Invalid message: insufficient length for HMAC");
            }

            hmac = new byte[hmacLength];
            Buffer.BlockCopy(receivedMessage, 0, hmac, 0, hmacLength);

            messageContent = new byte[receivedMessage.Length - hmacLength];
            Buffer.BlockCopy(receivedMessage, hmacLength, messageContent, 0, messageContent.Length);
        }

        private static byte[] GenerateHmac(byte[] message, byte[] key)
        {
            using (var hmac = new HMACSHA256(key))
            {
                return hmac.ComputeHash(message);
            }
        }

        private static bool SlowEquals(byte[] a, byte[] b)
        {
            uint diff = (uint)a.Length ^ (uint)b.Length;
            for (int i = 0; i < a.Length && i < b.Length; i++)
            {
                diff |= (uint)(a[i] ^ b[i]);
            }
            return diff == 0;
        }

        public byte[] ToByteArray()
        {
            return this.ToBigEndianByteArray();
        }

        protected void EncodeUlong(MemoryStream memStream, ulong value)
        {
            if (null == memStream)
            {
                throw new ArgumentNullException("memStream");
            }

            var bytes = BitConverter.GetBytes(value);
            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            memStream.Write(bytes, 0, bytes.Length);
        }

        protected void EncodeBool(MemoryStream memStream, bool value)
        {
            this.EncodeUlong(memStream, value ? 1UL : 0);
        }

        protected void EncodeBytes(MemoryStream memStream, byte[] value)
        {
            if (null == value)
            {
                throw new ArgumentNullException("value");
            }

            this.EncodeUlong(memStream, (ulong)value.Length);
            memStream.Write(value, 0, value.Length);
        }

        protected void EncodeHeader(MemoryStream memStream)
        {
            this.EncodeUlong(memStream, CaseId);
        }
    }
}
