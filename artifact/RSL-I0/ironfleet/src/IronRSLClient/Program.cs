using System;
using System.Linq;
using System.Numerics;
using System.Threading;
using System.IO;
using System.Net;
using System.Collections.Generic;

namespace IronRSLClient
{
    class Program
    {
        static void usage()
        {
          Console.Write(@"
Usage:  dotnet IronRSLClient.dll [key=value]...

Allowed keys:
  clientip - IP address this client should bind to (default 127.0.0.1)
  clientport - Port this client should bind to (default 6000)
  ip1 - IP address of first IronRSL host (default 127.0.0.1)
  ip2 - IP address of second IronRSL host (default 127.0.0.1)
  ip3 - IP address of third IronRSL host (default 127.0.0.1)
  port1 - port of first IronRSL host (default 4001)
  port2 - port of first IronRSL host (default 4002)
  port3 - port of first IronRSL host (default 4003)
  nthreads - number of client threads to run (default 1)
  duration - duration of experiment in seconds (default 60)
  initialseqno - first sequence number each thread uses (default 0)

If nthreads > 1, then each thread will use a different port number,
using consecutive port numbers starting with clientport.

NOTE: Each client endpoint is expected to use strictly increasing
sequence numbers. So if you run this program multiple times, either:
(1) use a different clientip, (2) use a clientport that causes
different ports to be used, or (3) use an initialseqno greater than
any sequence number seen in previous runs (e.g., if the previous run
output #req100, use at least initialseqno=101)
");
        }

        static void Main(string[] args)
{
    int num_threads = 1;
    ulong experiment_duration = 60;
    IPAddress client_ip = IPAddress.Parse("127.0.0.1");
    // IPAddress ip1 = IPAddress.Parse("130.245.173.104");
    // IPAddress ip2 = IPAddress.Parse("130.245.173.104");
    // IPAddress ip3 = IPAddress.Parse("130.245.173.104");
    IPAddress ip1 = IPAddress.Parse("127.0.0.1");
    IPAddress ip2 = IPAddress.Parse("127.0.0.1");
    IPAddress ip3 = IPAddress.Parse("127.0.0.1");
    int client_port = 6000;
    int port1 = 4101;
    int port2 = 4102;
    int port3 = 4103;
    ulong initial_seq_no = 0;

    foreach (var arg in args)
    {
        var pos = arg.IndexOf("=");
        if (pos < 0) { usage(); return; }
        var key = arg.Substring(0, pos).ToLower();
        var value = arg.Substring(pos + 1);

        try {
            switch (key) {
                case "clientip": client_ip = IPAddress.Parse(value); break;
                case "ip1": ip1 = IPAddress.Parse(value); break;
                case "ip2": ip2 = IPAddress.Parse(value); break;
                case "ip3": ip3 = IPAddress.Parse(value); break;
                case "clientport": client_port = Convert.ToInt32(value); break;
                case "port1": port1 = Convert.ToInt32(value); break;
                case "port2": port2 = Convert.ToInt32(value); break;
                case "port3": port3 = Convert.ToInt32(value); break;
                case "nthreads": num_threads = Convert.ToInt32(value); break;
                case "duration": experiment_duration = Convert.ToUInt64(value); break;
                case "initialseqno": initial_seq_no = Convert.ToUInt64(value); break;
                default: usage(); return;
            }
        }
        catch (Exception e) { usage(); return; }
    }

    int[] num_req_cnt_a = new int[num_threads];
    double[] latency_cnt_ms_a = new double[num_threads];
    int[] instant_req_cnt_a = new int[num_threads]; 
    
    Array.Clear(num_req_cnt_a, 0, num_threads);
    Array.Clear(latency_cnt_ms_a, 0, num_threads);
    Array.Clear(instant_req_cnt_a, 0, num_threads);

    ClientBase.endpoints = new List<IPEndPoint>() {
        new IPEndPoint(ip1, port1),
        new IPEndPoint(ip2, port2),
        new IPEndPoint(ip3, port3)
    };
    ClientBase.my_addr = client_ip;

    HiResTimer.Initialize();
    Client.Trace("Client process starting " + num_threads + " running for " + experiment_duration + "s ...");

    Console.WriteLine("[[READY]]");

    var threads = ClientBase.StartThreads<Client>(num_threads, client_port, initial_seq_no, num_req_cnt_a, latency_cnt_ms_a, instant_req_cnt_a).ToArray();

    bool running = true;
    string logFilePath = "throughput_log.txt";
    StreamWriter logWriter = new StreamWriter(logFilePath, append: true);
    logWriter.AutoFlush = true; 

    Thread monitoringThread = new Thread(() =>
    {
        while (running)
        {
            int total_instant_requests = 0;
            for (int i = 0; i < num_threads; i++)
            {
                total_instant_requests += instant_req_cnt_a[i];
                instant_req_cnt_a[i] = 0;
            }

            string logMessage = $" {(double)total_instant_requests / 20.0} ";

            // Console.WriteLine("Instant Throughput: {0} req/ms", total_instant_requests / 5.0);
            // Console.WriteLine(logMessage);
            logWriter.WriteLine(logMessage);

            Thread.Sleep(20);
        }
    });
    monitoringThread.Start();

    if (experiment_duration == 0)
    {
        threads[0].Join();
    }
    else
    {
        Thread.Sleep((int)(experiment_duration) * 1000);
        running = false;
        monitoringThread.Join();
        Console.WriteLine("[[DONE]]");

        string resultFile = "experiment_result.txt";
        using (StreamWriter log = new StreamWriter(resultFile, append: true))
        {
            int total_num_req_cnt = 0;
            double total_latency_cnt_ms = 0;
            for (int i = 0; i < num_threads; ++i)
            {
                total_num_req_cnt += num_req_cnt_a[i];
                total_latency_cnt_ms += latency_cnt_ms_a[i];

                string msg = string.Format("Client {0} throughput {1} | avg latency ms {2}",
                                        i, num_req_cnt_a[i], latency_cnt_ms_a[i] / num_req_cnt_a[i]);
                Console.WriteLine(msg);
                log.WriteLine(msg);
            }

            string finalMsg = string.Format("Throughput {0} | avg latency ms {1}",
                                            total_num_req_cnt / (int)(experiment_duration - 8),
                                            total_latency_cnt_ms / total_num_req_cnt);

            Console.WriteLine(finalMsg);
            log.WriteLine("[[DONE]]");
            log.WriteLine(finalMsg);
            log.Flush();
        }
        Environment.Exit(0);
    }
    AppDomain.CurrentDomain.ProcessExit += (sender, eventArgs) =>
    {
        running = false;
        monitoringThread.Join();
        logWriter.Close();
    };
    }
    }
}
