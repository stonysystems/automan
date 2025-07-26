using IronfleetCommon;
using IronfleetIoFramework;
using IronRSLClient;
using System;
using System.Collections.Generic;
using System.IO;
using System.Net;
using System.Threading;
using System.Linq;

namespace IronRSLCounterClient
{
  public class IncrementRequest
  {
    public IncrementRequest() { }

    public byte[] Encode()
    {
      MemoryStream memStream = new MemoryStream();
      IoEncoder.WriteUInt64(memStream, 0);             // request type (0 = increment)
      return memStream.ToArray();
    }
  }

  public class IncrementReply
  {
    public UInt64 counterValue;

    private IncrementReply(UInt64 i_counterValue)
    {
      counterValue = i_counterValue;
    }
    
    public static IncrementReply Decode(byte[] bytes)
    {
      if (bytes.Length != 8) {
        Console.Error.WriteLine("Got invalid-length reply");
        return null;
      }

      UInt64 counterValue = IoEncoder.ExtractUInt64(bytes, 0);
      return new IncrementReply(counterValue);
    }
  }

  public class Client
  {
    public int id;
    public Params ps;
    public ServiceIdentity serviceIdentity;

    public int []num_req_cnt_a;
    public int []latency_cnt_ms_a;

    private Client(int i_id, Params i_ps, ServiceIdentity i_serviceIdentity, int []num_req_cnt_a_, int []latency_cnt_ms_a_)
    {
      id = i_id;
      ps = i_ps;
      serviceIdentity = i_serviceIdentity;

      num_req_cnt_a = num_req_cnt_a_;
      latency_cnt_ms_a = latency_cnt_ms_a_;
    }

    static public IEnumerable<Thread> StartThreads<T>(Params ps, ServiceIdentity serviceIdentity, int []num_req_cnt_a, int []latency_cnt_ms_a)
    {
      for (int i = 0; i < ps.NumThreads; ++i)
      {
        Client c = new Client(i, ps, serviceIdentity, num_req_cnt_a, latency_cnt_ms_a);
        Thread t = new Thread(c.Run);
        t.Start();
        yield return t;
      }
    }

    private void Run()
    {
      RSLClient rslClient = new RSLClient(serviceIdentity, "Counter", ps.Verbose);

      Thread.Sleep(3000);

      for (int requestNum = 1; true; ++requestNum)
      {
        var request = new IncrementRequest();
        byte[] requestBytes = request.Encode();
        var startTime = HiResTimer.Ticks;
        byte[] replyBytes = rslClient.SubmitRequest(requestBytes);
        var endTime = HiResTimer.Ticks;
        var reply = IncrementReply.Decode(replyBytes);
        if (ps.PrintReplies) {
          Console.WriteLine("Received increment reply with counter {0}", reply.counterValue);
        }
        // Console.WriteLine("#req {0} {1} {2}",
        //                   id,
        //                   requestNum,
        //                   HiResTimer.TicksToMilliseconds(endTime - startTime));

        num_req_cnt_a[id] += 1;
      	latency_cnt_ms_a[id] += (int) HiResTimer.TicksToMilliseconds(endTime - startTime);
      }
    }
  }
}
