using IronfleetCommon;
using IronfleetIoFramework;
using System;
using System.Linq;
using System.Numerics;
using System.Threading;
using System.IO;
using System.Net;
using System.Collections.Generic;

namespace IronRSLKVClient
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet IronRSLKVClient.dll <service> [key=value]...

  <service>      - file path of the service description

Allowed keys:
  nthreads       - number of client threads to run (default 1)
  duration       - duration of experiment in seconds (default 60)
  setfraction    - fraction of requests that are sets (default 0.25)
  deletefraction - fraction of requests that are deletes (default 0.05)
  print          - print requests and replies (false or true, default false)
  verbose        - print verbose output (false or true, default false)
");
    }

    static void Main(string[] args)
    {
      Params ps = new Params();

      foreach (var arg in args)
      {
        if (!ps.ProcessCommandLineArgument(arg)) {
          usage();
          return;
        }
      }

      if (!ps.Validate()) {
        usage();
        return;
      }

      var serviceIdentity = ServiceIdentity.ReadFromFile(ps.ServiceFileName);
      if (serviceIdentity == null) {
        return;
      }

      HiResTimer.Initialize();
      if (ps.Verbose) {
        Console.WriteLine("Client process starting {0} threads running for {1} s...", ps.NumThreads, ps.ExperimentDuration);
      }

      Console.WriteLine("[[READY]]");
      
      int[] num_req_cnt_a = new int[ps.NumThreads];
      double[] latency_cnt_ms_a = new double[ps.NumThreads];
      
      Array.Clear(num_req_cnt_a, 0, ps.NumThreads);
      Array.Clear(latency_cnt_ms_a, 0, ps.NumThreads);
            
      // Start the experiment
      var threads = Client.StartThreads<Client>(ps, serviceIdentity, num_req_cnt_a, latency_cnt_ms_a).ToArray();

      if (ps.ExperimentDuration == 0)
      {
        threads[0].Join();
      }
      else
      {
        Thread.Sleep((int)ps.ExperimentDuration * 1000);
        Console.Out.WriteLine("[[DONE]]");
        Console.Out.Flush();
        
        int total_num_req_cnt = 0;
        double total_latency_cnt_ms = 0;
        
        for (int i = 0; i < ps.NumThreads; ++i)
        {
        	int num_req_cnt = num_req_cnt_a[i];
        	double latency_cnt_ms = latency_cnt_ms_a[i];
			
          total_num_req_cnt += num_req_cnt;
          total_latency_cnt_ms += latency_cnt_ms;
        }
        
        string finalMsg = string.Format("throughput {0} | avg latency ms {1:F2}",
          total_num_req_cnt / (int)ps.ExperimentDuration,
          total_latency_cnt_ms / total_num_req_cnt);
        
        Console.WriteLine(finalMsg);

        string resultFile = "experiment_result.txt";
        using (StreamWriter log = new StreamWriter(resultFile, append: false))
        {
            // log.WriteLine("[[DONE]]");
            log.WriteLine(finalMsg);
            log.Flush();
        }
        
        Environment.Exit(0);
      }
    }
  }
}
