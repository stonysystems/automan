using IronfleetCommon;
using IronRSLClient;
using IronfleetIoFramework;
using KVMessages;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Text;
using System.Threading;

namespace IronRSLKVClient
{
  public class Client
  {
    public int id;
    public Params ps;
    public ServiceIdentity serviceIdentity;
    
    public int []num_req_cnt_a;
    public double []latency_cnt_ms_a;

    private Client(int i_id, Params i_ps, ServiceIdentity i_serviceIdentity, int []num_req_cnt_a_, double []latency_cnt_ms_a_)
    {
      id = i_id;
      ps = i_ps;
      serviceIdentity = i_serviceIdentity;
      
      num_req_cnt_a = num_req_cnt_a_;
      latency_cnt_ms_a = latency_cnt_ms_a_;
    }

    static public IEnumerable<Thread> StartThreads<T>(Params ps, ServiceIdentity serviceIdentity, int []num_req_cnt_a, double []latency_cnt_ms_a)
    {
      for (int i = 0; i < ps.NumThreads; ++i)
      {
        Client c = new Client(i, ps, serviceIdentity, num_req_cnt_a, latency_cnt_ms_a);
        Thread t = new Thread(c.Run);
        t.Start();
        yield return t;
      }
    }
  
    private static KVRequest GetRandomRequest(Random rng, Params ps)
    {
      int keySelector = rng.Next(26);
      char k = (char)('a' + keySelector);
      StringBuilder keyBuilder = new StringBuilder();
      keyBuilder.Append(k);
      keyBuilder.Append(k);
      keyBuilder.Append(k);
      string key = keyBuilder.ToString();
      
      int reqTypeSelector = rng.Next();
      if (reqTypeSelector < ps.SetFraction * Int32.MaxValue) {
        char v = (char)('A' + keySelector);
        StringBuilder valBuilder = new StringBuilder();
        valBuilder.Append(v);
        valBuilder.Append(v);
        valBuilder.Append(v);
        valBuilder.Append(v);
        valBuilder.Append(rng.Next(100000));
        string val = valBuilder.ToString();
        if (ps.PrintRequestsAndReplies) {
          // Console.WriteLine("Submitting set request for {0} => {1}", key, val);
        }
        return new KVSetRequest(key, val);
      }
      else if (reqTypeSelector < (ps.SetFraction + ps.DeleteFraction) * Int32.MaxValue) {
        if (ps.PrintRequestsAndReplies) {
          // Console.WriteLine("Submitting delete request for {0}", key);
        }
        return new KVDeleteRequest(key);
      }
      else {
        if (ps.PrintRequestsAndReplies) {
          // Console.WriteLine("Submitting get request for {0}", key);
        }
        return new KVGetRequest(key);
      }
    }

    private void Run()
    {
      RSLClient rslClient = new RSLClient(serviceIdentity, "KV", ps.Verbose);

      Thread.Sleep(3000);

      Random rng = new Random();

      for (int requestNum = 1; true; ++requestNum)
      {
        KVRequest request = GetRandomRequest(rng, ps);
        byte[] requestBytes = request.Encode();
        var startTime = HiResTimer.Ticks;
        byte[] replyBytes = rslClient.SubmitRequest(requestBytes);
        var endTime = HiResTimer.Ticks;
        KVReply reply = KVReply.Decode(replyBytes, 0);

        if (ps.PrintRequestsAndReplies) {
          // Console.WriteLine("Received reply of type {0}", reply.ReplyType);
          // if (reply is KVGetFoundReply gfr) {
          //   Console.WriteLine("Value obtained for get was {0}", gfr.Val);
          // }
        }
        
        // Console.WriteLine("#req {0} {1} {2}",
        //                   id,
        //                  requestNum,
        //                  HiResTimer.TicksToMilliseconds(endTime - startTime));
        
      	num_req_cnt_a[id] += 1;
      	// latency_cnt_ms_a[id] += (int) HiResTimer.TicksToMilliseconds(endTime - startTime);
        latency_cnt_ms_a[id] += HiResTimer.TicksToMilliseconds(endTime - startTime);
      }
    }
  }
}
