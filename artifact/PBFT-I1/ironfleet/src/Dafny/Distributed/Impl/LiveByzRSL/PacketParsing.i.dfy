include "../../Common/Collections/Maps.i.dfy"
include "../../Protocol/ByzRSL/Configuration.i.dfy"
include "../../Protocol/ByzRSL/Message.i.dfy"
include "../../Protocol/ByzRSL/Types.i.dfy"
include "../../Protocol/ByzRSL/Environment.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "../ByzRSL/CTypes.i.dfy"
include "../ByzRSL/CMessage.i.dfy"
include "CMessageRefinements.i.dfy"

module LiveByzRSL__PacketParsing_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened Collections__Maps_i
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__CMessage_i
  // import opened LiveByzRSL__CMessageRefinements_i
  import opened LiveByzRSL__Configuration_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__Environment_i
  import opened LiveByzRSL__Message_i
  import opened LiveByzRSL__Types_i
  import opened Common__GenericMarshalling_i
  import opened Common__NodeIdentity_i
  import opened Common__UdpClient_i
  import opened Common__Util_i
    // import opened AppStateMachine_s
  import opened Environment_s
  import opened Math__mul_i
  import opened Math__mul_nonlinear_i

  ////////////////////////////////////////////////////////////////////
  //    Grammars for the Paxos types
  ////////////////////////////////////////////////////////////////////
  function method EndPoint_grammar() : G { GUint64 }
  function method CRequest_grammar() : G { GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar()]) }
  // function method CRequest_grammar() : G { GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar(), GUint64, GUint64, GUint64, GUint64]) }
  function method CRequestBatch_grammar() : G { GArray(CRequest_grammar()) }
  function method CReply_grammar() : G { GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar()]) }
  function method CBallot_grammar() : G { GTuple([GUint64, GUint64]) }
  function method COperationNumber_grammar() : G { GUint64 }
  function method CVote_grammar() : G { GTuple([CBallot_grammar(), CRequestBatch_grammar()])}
  function method CMap_grammar(key:G, val:G) : G { GArray(GTuple([key, val])) }
  function method CVotes_grammar() : G { GArray(GTuple([COperationNumber_grammar(), CVote_grammar()])) }
  function method CReplyCache_grammar() : G { GArray(GTuple([EndPoint_grammar(), CReply_grammar()])) }

  ////////////////////////////////////////////////////////////////////
  //    Grammars for the Paxos messages
  ////////////////////////////////////////////////////////////////////
  function method CMessage_Request_grammar() : G { GTuple([GUint64, CAppMessage_grammar()]) }
  function method CMessage_1a_grammar() : G { CBallot_grammar() }
  function method CMessage_1b_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar(), CVotes_grammar()]) }
  function method CMessage_1c_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar(), CRequestBatch_grammar()]) }
  function method CMessage_2av_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar(), CRequestBatch_grammar()]) }
  function method CMessage_2b_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar(), CRequestBatch_grammar()]) }
  function method CMessage_Heartbeat_grammar() : G { GTuple([CBallot_grammar(), GUint64, COperationNumber_grammar()]) }
  function method CMessage_Reply_grammar() : G { GTuple( [GUint64, CAppMessage_grammar()] ) }
  // function method CMessage_AppStateRequest_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar()]) }
  // function method CMessage_AppStateSupply_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar(), CAppState_grammar(), CReplyCache_grammar()]) }
  function method CMessage_StartingPhase2_grammar() : G { GTuple([CBallot_grammar(), COperationNumber_grammar()]) }

  function method CMessage_grammar() : G { GTaggedUnion([
                                                          CMessage_Request_grammar(),
                                                          CMessage_1a_grammar(),
                                                          CMessage_1b_grammar(),
                                                          CMessage_1c_grammar(),
                                                          CMessage_2av_grammar(),
                                                          CMessage_2b_grammar(),
                                                          CMessage_Heartbeat_grammar(),
                                                          CMessage_Reply_grammar(),
                                                          // CMessage_AppStateRequest_grammar(),
                                                          // CMessage_AppStateSupply_grammar(),
                                                          CMessage_StartingPhase2_grammar()
                                                        ]) }

  predicate NetPacketBound(data:seq<byte>)
  {
    |data| < MaxPacketSize()
  }

  ////////////////////////////////////////////////////////////////////
  //    64-bit Limits
  ////////////////////////////////////////////////////////////////////

  predicate CRequestBatchIs64Bit(batch:CRequestBatch)
  {
    |batch| < 0x1_0000_0000_0000_0000
  }

  predicate CVoteIs64Bit(vote:CVote)
  {
    CRequestBatchIs64Bit(vote.max_val)
  }

  predicate CVotesIs64Bit(votes:CVotes)
  {
    && |votes| < 0x1_0000_0000_0000_0000
    && (forall opn :: opn in votes ==> CVoteIs64Bit(votes[opn]))
  }

  predicate CReplyCacheIs64Bit(rc:CReplyCache)
  {
    |rc| < 0x1_0000_0000_0000_0000
  }

  predicate CMessageIs64Bit(msg:CMessage)
  {
    match msg
    case CMessage_Invalid => true
    case CMessage_Request(seqno, val) => true
    case CMessage_1a(bal) => true
    case CMessage_1b(bal, log_truncation_point, votes) => CVotesIs64Bit(votes)
    case CMessage_1c(bal, opn, batch) => CRequestBatchIs64Bit(batch)
    case CMessage_2av(bal, opn, batch) => CRequestBatchIs64Bit(batch)
    case CMessage_2b(bal, opn, batch) => CRequestBatchIs64Bit(batch)
    case CMessage_Heartbeat(bal, suspicious, opn) => true
    case CMessage_Reply(seqno, reply) => true
    // case CMessage_AppStateRequest(bal, opn) => true
    // case CMessage_AppStateSupply(bal, opn, app, rc) => CReplyCacheIs64Bit(rc)
    case CMessage_StartingPhase2(bal, log_truncation_point) => true
  }

  ////////////////////////////////////////////////////////////////////
  //    Parsing
  ////////////////////////////////////////////////////////////////////

  function method parse_EndPoint(val:V) : EndPoint
    requires ValInGrammar(val, EndPoint_grammar())
    ensures  EndPointIsAbstractable(parse_EndPoint(val))
  {
    if val.u <= 0xffffffffffff then
      ConvertUint64ToEndPoint(val.u)
    else
      EndPoint([0,0,0,0], 0)
  }

  // function method parse_Request(val:V) : CRequest
  //   requires ValInGrammar(val, CRequest_grammar())
  //   ensures  CRequestIsAbstractable(parse_Request(val))
  // {
  //   assert ValInGrammar(val.t[0], CRequest_grammar().t[0]);      // OBSERVE
  //   assert ValInGrammar(val.t[1], CRequest_grammar().t[1]);      // OBSERVE
  //   assert ValInGrammar(val.t[2], CRequest_grammar().t[2]);      // OBSERVE
  //   assert ValInGrammar(val.t[3], CRequest_grammar().t[3]);
  //   assert ValInGrammar(val.t[4], CRequest_grammar().t[4]);
  //   assert ValInGrammar(val.t[5], CRequest_grammar().t[5]);
  //   assert ValInGrammar(val.t[6], CRequest_grammar().t[6]);
  //   var ep := parse_EndPoint(val.t[0]);
  //   CRequest(ep, val.t[1].u, parse_AppMessage(val.t[2]), val.t[3].u, val.t[4].u, val.t[5].u, val.t[6].u)
  // }

  function method parse_Request(val:V) : CRequest
    requires ValInGrammar(val, CRequest_grammar())
    ensures  CRequestIsAbstractable(parse_Request(val))
  {
    assert ValInGrammar(val.t[0], CRequest_grammar().t[0]);      // OBSERVE
    assert ValInGrammar(val.t[1], CRequest_grammar().t[1]);      // OBSERVE
    assert ValInGrammar(val.t[2], CRequest_grammar().t[2]);      // OBSERVE
    var ep := parse_EndPoint(val.t[0]);
    CRequest(ep, val.t[1].u as int, parse_AppMessage(val.t[2]))
  }

  function parse_RequestBatch(val:V) : CRequestBatch
    requires ValInGrammar(val, CRequestBatch_grammar())
    ensures  |parse_RequestBatch(val)| == |val.a|
    ensures  forall i :: 0 <= i < |parse_RequestBatch(val)| ==> parse_RequestBatch(val)[i] == parse_Request(val.a[i])
    ensures  CRequestBatchIsAbstractable(parse_RequestBatch(val))
    ensures  ValidVal(val) ==> CRequestBatchIs64Bit(parse_RequestBatch(val))
    decreases |val.a|
  {
    if |val.a| == 0 then
      []
    else
      var req := parse_Request(val.a[0]);
      var restVal:V := VArray(val.a[1..]);
      var rest := parse_RequestBatch(restVal);
      [req] + rest
  }

  /*
  method parse_RequestBatchIter(val:V) returns (batch:CRequestBatch)
    requires ValInGrammar(val, CRequestBatch_grammar())
    requires ValidVal(val)
    ensures |batch| == |val.a|
    ensures forall i :: 0 <= i < |batch| ==> batch[i] == parse_Request(val.a[i])
  {
    batch := [];
  
    var i:uint64 := 0;
    while i < |val.a| as uint64 
      invariant 0 <= int(i) <= |val.a|
      invariant int(i) == |batch|
      invariant forall j :: 0 <= j < int(i) ==> batch[j] == parse_Request(val.a[j])
    {
      var req := parse_Request(val.a[i]);
      batch := batch + [req];
      i := i + 1;
    }
  }
  */

  method Parse_RequestBatch(val:V) returns (batch:CRequestBatch)
    requires ValInGrammar(val, CRequestBatch_grammar())
    requires ValidVal(val)
    ensures |batch| == |val.a|
    ensures  CRequestBatchIs64Bit(batch)
    ensures  forall i :: 0 <= i < |batch| ==> batch[i] == parse_Request(val.a[i])
    ensures  batch == parse_RequestBatch(val)
    ensures  CRequestBatchIsAbstractable(batch)
  {
    var batchArr := new CRequest[|val.a| as uint64];

    var i:uint64 := 0;
    while i < |val.a| as uint64
      invariant 0 <= i as int <= |val.a|
      invariant forall j :: 0 <= j < i as int ==> batchArr[j] == parse_Request(val.a[j])
    {
      var req := parse_Request(val.a[i]);
      batchArr[i] := req;
      i := i + 1;
    }
    batch := batchArr[..];
  }

  function method parse_Reply(val:V) : CReply
    requires ValInGrammar(val, CReply_grammar())
    ensures  CReplyIsAbstractable(parse_Reply(val))
  {
    assert ValInGrammar(val.t[0], CReply_grammar().t[0]);      // OBSERVE
    assert ValInGrammar(val.t[1], CReply_grammar().t[1]);      // OBSERVE
    assert ValInGrammar(val.t[2], CReply_grammar().t[2]);      // OBSERVE
    var ep := parse_EndPoint(val.t[0]);
    CReply(ep, val.t[1].u as int, parse_AppMessage(val.t[2]))
  }

  function method parse_Ballot(val:V) : CBallot
    requires ValInGrammar(val, CBallot_grammar())
    ensures  CBallotIsAbstractable(parse_Ballot(val))
  {
    assert ValInGrammar(val.t[0], CBallot_grammar().t[0]);      // OBSERVE
    assert ValInGrammar(val.t[1], CBallot_grammar().t[1]);      // OBSERVE
    CBallot(val.t[0].u as int, val.t[1].u as int)
  }

  function method parse_OperationNumber(val:V) : COperationNumber
    requires ValInGrammar(val, COperationNumber_grammar())
    // ensures  COperationNumberIsAbstractable(parse_OperationNumber(val))
  {
    val.u as int
  }

  function parse_Vote(val:V) : CVote
    requires ValInGrammar(val, CVote_grammar())
    ensures  CVoteIsAbstractable(parse_Vote(val))
    ensures  ValidVal(val) ==> CVoteIs64Bit(parse_Vote(val))
  {
    CVote(parse_Ballot(val.t[0]), parse_RequestBatch(val.t[1]))
  }

  method Parse_Vote(val:V) returns (vote:CVote)
    requires ValInGrammar(val, CVote_grammar())
    requires ValidVal(val)
    ensures  parse_Vote(val) == vote
    ensures  CVoteIs64Bit(vote)
  {
    var batch := Parse_RequestBatch(val.t[1]);
    vote := CVote(parse_Ballot(val.t[0]), batch);
  }


  // Abandoned for now, since the marshalling side is all methods, so we can't easily make it higher order
  // 
  //function method parse_Map<KT, VT>(val:V, parse_key:V->KT, parse_val:V->VT, key_grammar:G, val_grammar:G) : map<KT, VT>
  //  requires ValInGrammar(val, CMap_grammar(key_grammar, val_grammar))
  //  requires forall v :: parse_key.requires(v) && parse_val.requires(v)
  //  reads parse_key.reads, parse_val.reads;
  //  decreases |val.a|
  //{
  //  if |val.a| == 0 then
  //    map []
  //  else
  //    var tuple := val.a[0];
  //    assert ValInGrammar(tuple, CMap_grammar(key_grammar, val_grammar).elt);
  //    assert ValInGrammar(tuple.t[0], CMap_grammar(key_grammar, val_grammar).elt.t[0]); // OBSERVE
  //    assert ValInGrammar(tuple.t[1], CMap_grammar(key_grammar, val_grammar).elt.t[1]); // OBSERVE
  //    var k := parse_key(tuple.t[0]);
  //    var v := parse_val(tuple.t[1]);
  //    var others := parse_Map(VArray(val.a[1..]), parse_key, parse_val, key_grammar, val_grammar);
  //    var m := others[k := v];
  //    m
  //}

  function parse_Votes(val:V) : CVotes
    requires ValInGrammar(val, CVotes_grammar())
    ensures  CVotesIsAbstractable(parse_Votes(val))
    ensures  |parse_Votes(val)| <= |val.a|
    ensures  ValidVal(val) ==> CVotesIs64Bit(parse_Votes(val))
    decreases |val.a|
  {
    if |val.a| == 0 then
      map []
    else
      var tuple := val.a[0];
      assert ValInGrammar(tuple, CVotes_grammar().elt);
      assert ValInGrammar(tuple.t[0], CVotes_grammar().elt.t[0]); // OBSERVE
      assert ValInGrammar(tuple.t[1], CVotes_grammar().elt.t[1]); // OBSERVE
      var op := parse_OperationNumber(tuple.t[0]);
      var vote := parse_Vote(tuple.t[1]);
      var others := parse_Votes(VArray(val.a[1..]));
      calc {
          ValidVal(val);
      ==> { assert val.a[0] in val.a; } ValidVal(val.a[0]);
      ==> ValidVal(tuple);
      ==> { assert tuple.t[1] in tuple.t; } ValidVal(tuple.t[1]);
      ==> CVoteIs64Bit(vote);
      }
      var m := others[op := vote];
      // assert COperationNumberIsAbstractable(op);
      // CVotes(m)
      m
  }

  method Parse_Votes(val:V) returns (votes:CVotes)
    requires ValInGrammar(val, CVotes_grammar())
    requires ValidVal(val)
    ensures  CVotesIsAbstractable(votes)
    ensures  CVotesIs64Bit(votes)
    decreases |val.a|
    ensures votes == parse_Votes(val)
  {
    if |val.a| as uint64 == 0 {
      votes := map [];
    } else {
      var tuple := val.a[0];
      assert ValInGrammar(tuple, CVotes_grammar().elt);
      assert ValInGrammar(tuple.t[0], CVotes_grammar().elt.t[0]); // OBSERVE
      assert ValInGrammar(tuple.t[1], CVotes_grammar().elt.t[1]); // OBSERVE
      calc ==> {
        ValidVal(val);
        ValidVal(tuple);
        ValidVal(tuple.t[1]);
      }
      var op := parse_OperationNumber(tuple.t[0]);
      var vote := Parse_Vote(tuple.t[1]);
      var others := Parse_Votes(VArray(val.a[1..]));
      var m := others[op := vote];
      votes := m;
    }
  }

  function method parse_ReplyCache(val:V) : CReplyCache
    requires ValInGrammar(val, CReplyCache_grammar())
    ensures  CReplyCacheIsAbstractable(parse_ReplyCache(val))
    ensures  |parse_ReplyCache(val)| <= |val.a|
    ensures  ValidVal(val) ==> CReplyCacheIs64Bit(parse_ReplyCache(val))
    decreases |val.a|
  {
    if |val.a| == 0 then
      map []
    else
      var tuple := val.a[0];
      assert ValInGrammar(tuple, CReplyCache_grammar().elt);
      assert ValInGrammar(tuple.t[0], CReplyCache_grammar().elt.t[0]); // OBSERVE
      assert ValInGrammar(tuple.t[1], CReplyCache_grammar().elt.t[1]); // OBSERVE
      var e := parse_EndPoint(tuple.t[0]);
      var reply := parse_Reply(tuple.t[1]);
      var others := parse_ReplyCache(VArray(val.a[1..]));
      var m := others[e := reply];
      assert forall e' :: e' in m ==> EndPointIsValidIPV4(e');
      assert forall e' :: e' in m ==> CReplyIsAbstractable(m[e']);
      m
  }

  function method parse_Message_Request(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Request_grammar())
    ensures  CMessageIsAbstractable(parse_Message_Request(val))
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_Request(val))
  {
    assert ValInGrammar(val.t[0], CMessage_Request_grammar().t[0]);      // OBSERVE
    assert ValInGrammar(val.t[1], CMessage_Request_grammar().t[1]);      // OBSERVE
    CMessage_Request(val.t[0].u as int, parse_AppMessage(val.t[1]))
  }

  function method parse_Message_1a(val:V) : CMessage
    requires ValInGrammar(val, CMessage_1a_grammar())
    ensures  CMessageIsAbstractable(parse_Message_1a(val))
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_1a(val))
  {
    CMessage_1a(parse_Ballot(val))
  }

  function parse_Message_1b(val:V) : CMessage
    requires ValInGrammar(val, CMessage_1b_grammar())
    ensures  CMessageIsAbstractable(parse_Message_1b(val))
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_1b(val))
  {
    CMessage_1b(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), parse_Votes(val.t[2]))
  }

  method Parse_Message_1b(val:V) returns (msg:CMessage)
    requires ValInGrammar(val, CMessage_1b_grammar())
    requires ValidVal(val)
    ensures  msg == parse_Message_1b(val)
    ensures  CMessageIsAbstractable(msg)
    ensures  CMessageIs64Bit(msg)
  {
    var votes := Parse_Votes(val.t[2]);
    msg := CMessage_1b(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), votes);
  }

  function parse_Message_1c(val:V) : CMessage
    requires ValInGrammar(val, CMessage_1c_grammar())
    ensures  CMessageIsAbstractable(parse_Message_1c(val))
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_1c(val))
  {
    CMessage_1c(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), parse_RequestBatch(val.t[2]))
  }

  method Parse_Message_1c(val:V) returns (msg:CMessage)
    requires ValInGrammar(val, CMessage_1c_grammar())
    requires ValidVal(val)
    ensures  msg == parse_Message_1c(val)
    ensures  CMessageIsAbstractable(msg)
    ensures  CMessageIs64Bit(msg)
  {
    var batch := Parse_RequestBatch(val.t[2]);
    msg := CMessage_1c(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), batch);
  }

  function parse_Message_2av(val:V) : CMessage
    requires ValInGrammar(val, CMessage_2av_grammar())
    ensures  CMessageIsAbstractable(parse_Message_2av(val))
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_2av(val))
  {
    CMessage_2av(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), parse_RequestBatch(val.t[2]))
  }

  method Parse_Message_2av(val:V) returns (msg:CMessage)
    requires ValInGrammar(val, CMessage_2av_grammar())
    requires ValidVal(val)
    ensures  msg == parse_Message_2av(val)
    ensures  CMessageIsAbstractable(msg)
    ensures  CMessageIs64Bit(msg)
  {
    var batch := Parse_RequestBatch(val.t[2]);
    msg := CMessage_2av(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), batch);
  }

  function parse_Message_2b(val:V) : CMessage
    requires ValInGrammar(val, CMessage_2b_grammar())
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_2b(val))
  {
    CMessage_2b(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), parse_RequestBatch(val.t[2]))
  }

  method Parse_Message_2b(val:V) returns (msg:CMessage)
    requires ValInGrammar(val, CMessage_2b_grammar())
    requires ValidVal(val)
    ensures  msg == parse_Message_2b(val)
    ensures  CMessageIsAbstractable(msg)
    ensures  CMessageIs64Bit(msg)
  {
    var batch := Parse_RequestBatch(val.t[2]);
    msg := CMessage_2b(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), batch);
  }

  function method parse_Message_Heartbeat(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Heartbeat_grammar())
    ensures  CMessageIsAbstractable(parse_Message_Heartbeat(val))
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_Heartbeat(val))
  {
    assert ValInGrammar(val.t[1], CMessage_Heartbeat_grammar().t[1]);      // OBSERVE
    CMessage_Heartbeat(parse_Ballot(val.t[0]), val.t[1].u != 0, parse_OperationNumber(val.t[2]))
  }

  function method parse_Message_Reply(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Reply_grammar())
    ensures  CMessageIsAbstractable(parse_Message_Reply(val))
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_Reply(val))
  {
    assert ValInGrammar(val.t[0], CMessage_Reply_grammar().t[0]);      // OBSERVE
    assert ValInGrammar(val.t[1], CMessage_Reply_grammar().t[1]);      // OBSERVE
    CMessage_Reply(val.t[0].u as int, parse_AppMessage(val.t[1]))
  }

  // function method parse_Message_AppStateRequest(val:V) : CMessage
  //   requires ValInGrammar(val, CMessage_AppStateRequest_grammar())
  //   ensures  CMessageIsAbstractable(parse_Message_AppStateRequest(val))
  //   ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_AppStateRequest(val))
  // {
  //   CMessage_AppStateRequest(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]))
  // }

  // function method parse_Message_AppStateSupply(val:V) : CMessage
  //   requires ValInGrammar(val, CMessage_AppStateSupply_grammar())
  //   ensures  CMessageIsAbstractable(parse_Message_AppStateSupply(val))
  //   ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_AppStateSupply(val))
  // {
  //   // assert ValInGrammar(val.t[2], GByteArray);
  //   CMessage_AppStateSupply(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), parse_AppState(val.t[2]), parse_ReplyCache(val.t[3]))
  //   // CMessage_AppStateSupply(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]), val.t[2].b)
  // }

  function method parse_Message_StartingPhase2(val:V) : CMessage
    requires ValInGrammar(val, CMessage_StartingPhase2_grammar())
    ensures  CMessageIsAbstractable(parse_Message_StartingPhase2(val))
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message_StartingPhase2(val))
  {
    CMessage_StartingPhase2(parse_Ballot(val.t[0]), parse_OperationNumber(val.t[1]))
  }


  function parse_Message(val:V) : CMessage
    requires ValInGrammar(val, CMessage_grammar())
    ensures  CMessageIsAbstractable(parse_Message(val))
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message(val))
  {
    if val.c == 0 then
      parse_Message_Request(val.val)
    else if val.c == 1 then
      parse_Message_1a(val.val)
    else if val.c == 2 then
      parse_Message_1b(val.val)
    else if val.c == 3 then
      parse_Message_1c(val.val)
    else if val.c == 4 then
      parse_Message_2av(val.val)
    else if val.c == 5 then
      parse_Message_2b(val.val)
    else if val.c == 6 then
      parse_Message_Heartbeat(val.val)
    else if val.c == 7 then
      parse_Message_Reply(val.val)
    // else if val.c == 8 then
    //   parse_Message_AppStateRequest(val.val)
    // else if val.c == 9 then
    //   parse_Message_AppStateSupply(val.val)
    else if val.c == 8 then
      parse_Message_StartingPhase2(val.val)
    else
      assert false;       // Should never get here
      parse_Message_Request(val)
  }

  method Parse_Message(val:V) returns (msg:CMessage)
    requires ValInGrammar(val, CMessage_grammar())
    requires ValidVal(val)
    ensures	 msg == parse_Message(val)
    ensures	 !msg.CMessage_Invalid?
    ensures	 CMessageIsAbstractable(msg)
    ensures	 CMessageIs64Bit(msg)
  {
    if val.c == 0 {
      msg := parse_Message_Request(val.val);
    } else if val.c == 1 {
      msg := parse_Message_1a(val.val);
    } else if val.c == 2 {
      msg := Parse_Message_1b(val.val);
    } else if val.c == 3 {
      msg := Parse_Message_1c(val.val);
    } else if val.c == 4 {
      msg := Parse_Message_2av(val.val);
    } else if val.c == 5 {
      msg := Parse_Message_2b(val.val);
    } else if val.c == 6 {
      msg := parse_Message_Heartbeat(val.val);
    } else if val.c == 7 {
      msg := parse_Message_Reply(val.val);
    } 
    // else if val.c == 8 {
    //   msg := parse_Message_AppStateRequest(val.val);
    // } else if val.c == 9 {
    //   msg := parse_Message_AppStateSupply(val.val);
    // } 
    else if val.c == 8 {
      msg := parse_Message_StartingPhase2(val.val);
    } else {
      assert false;				// Should never get here
      msg := parse_Message_Request(val);
    }
  }

  function PaxosDemarshallData(data:seq<byte>) : CMessage
    ensures  CMessageIsAbstractable(PaxosDemarshallData(data))
  {
    if Demarshallable(data, CMessage_grammar()) then
      var val := DemarshallFunc(data, CMessage_grammar());
      parse_Message(val)
    else
      CMessage_Invalid()
  }

  method PaxosDemarshallDataMethod(data:array<byte>, msg_grammar:G) returns (msg:CMessage)
    requires data.Length < 0x1_0000_0000_0000_0000
    requires msg_grammar == CMessage_grammar()
    requires ValidGrammar(msg_grammar)
    ensures  CMessageIsAbstractable(msg)
    ensures  if Demarshallable(data[..], msg_grammar) then
               msg == PaxosDemarshallData(data[..])
             else
               msg.CMessage_Invalid?
    ensures  CMessageIs64Bit(msg)
  {
    var success, val := Demarshall(data, msg_grammar);
    if success {
      assert ValInGrammar(val, msg_grammar);
      msg := Parse_Message(val);
      assert !msg.CMessage_Invalid?;
    } else {
      msg := CMessage_Invalid();
    }
  }

  ////////////////////////////////////////////////////////////////////
  //    Can a value be marshalled?
  ////////////////////////////////////////////////////////////////////

  function Marshallable_1c(msg:CMessage) : bool
  {
    && msg.CMessage_1c?
    && CRequestBatchIsValid(msg.val_1c)
  }

  function Marshallable_2av(msg:CMessage) : bool
  {
    && msg.CMessage_2av?
    && CRequestBatchIsValid(msg.val_2av)
  }

  function Marshallable_2b(msg:CMessage) : bool
  {
    && msg.CMessage_2b?
    && CRequestBatchIsValid(msg.val_2b)
  }

  function Marshallable(msg:CMessage) : bool
  {
    && (!msg.CMessage_Invalid?)
    && (msg.CMessage_Request? ==> CAppMessageIsValid(msg.val))
    && (msg.CMessage_1a? ==> true)
    && (msg.CMessage_1b? ==> CVotesIsValid(msg.votes))
    && (msg.CMessage_1c? ==> Marshallable_1c(msg))
    && (msg.CMessage_2av? ==> Marshallable_2av(msg))
    && (msg.CMessage_2b? ==> Marshallable_2b(msg))
    && (msg.CMessage_Heartbeat? ==> true)
    && (msg.CMessage_Reply? ==> CAppMessageIsValid(msg.reply))
    // && (msg.CMessage_AppStateRequest? ==> true)
    // && (msg.CMessage_AppStateSupply? ==> AppStateMarshallable(msg.app_state)  && CReplyCacheIsValid(msg.reply_cache))
    && (msg.CMessage_StartingPhase2? ==> true)
  }

  function CMessageIsMarshallable(msg:CMessage) : bool
  {
    Marshallable(msg)
  }

  // predicate CPacketsIsMarshallable(cps:set<CPacket>)
  // {
  //   forall cp :: cp in cps ==> Marshallable(cp.msg)
  // }

  method DetermineIfValidVote(vote:CVote) returns (b:bool)
    requires CVoteIsAbstractable(vote)
    requires CVoteIs64Bit(vote)
    ensures b == CVoteIsValid(vote)
  {
    b := (|vote.max_val| as uint64) <= RequestBatchSizeLimit() as uint64;  // RequestBatchSizeLimit
  }

  // method DetermineIfValidVote(vote:CVote) returns (b:bool)
  //   requires CVoteIsAbstractable(vote)
  //   requires CVoteIs64Bit(vote)
  //   ensures b == CVoteIsValid(vote)
  // {
  //   var num_votes:uint64 := |vote.max_val| as uint64;
  //   if num_votes > RequestBatchSizeLimit() as uint64 {  // RequestBatchSizeLimit
  //     b := false;
  //     return;
  //   }

  //   var pos:uint64 := 0;
  //   while pos < num_votes
  //     invariant 0 <= pos <= num_votes
  //     invariant forall i :: 0 <= i < pos ==> CRequestIsValid(vote.max_val[i])
  //   {
  //     var c := vote.max_val[pos];
  //     if !CAppRequestMarshallable(c.request) || !EndPointIsValidPublicKey(c.client) {
  //       assert !CRequestIsValid(c);
  //       assert !CRequestBatchIsValid(vote.max_val);
  //       b := false;
  //       return;
  //     }
  //     pos := pos + 1;
  //   }

  //   b := true;
  // }

  method DetermineIfValidVotes(votes:CVotes) returns (b:bool)
    requires CVotesIsAbstractable(votes)
    requires CVotesIs64Bit(votes)
    ensures  b == CVotesIsValid(votes)
  {
    b := (|votes| as uint64) < max_votes_len() as uint64;  // max_votes_len
    if !b {
      return;
    }

    var keys := domain(votes);
    lemma_MapSizeIsDomainSize(keys, votes);
    while |keys| > 0
      invariant |keys| < max_votes_len()
      invariant forall opn :: opn in keys ==> opn in votes
      invariant forall opn :: opn in votes ==> opn in keys || CVoteIsValid(votes[opn])
      decreases |keys|
    {
      var opn :| opn in keys;
      keys := keys - {opn};
      b := DetermineIfValidVote(votes[opn]);
      if !b {
        return;
      }
    }
  }

  method DetermineIfValidRequestBatch(c:CRequestBatch) returns (b:bool)
    requires CRequestBatchIsAbstractable(c)
    requires CRequestBatchIs64Bit(c)
    ensures  b == CRequestBatchIsValid(c)
  {
    var n := |c| as uint64;
    b := n <= RequestBatchSizeLimit() as uint64;
    if !b {
      return;
    }

    var pos: uint64 := 0;
    while pos < n
      invariant 0 <= pos <= n
      invariant forall i :: 0 <= i < pos ==> CRequestIsValid(c[i])
    {
      // if !CRequestIsValid(c[pos]) {
      //   assert !CRequestIsValid(c[pos]);
      //   b := false;
      //   return;
      // }

      var a := c[pos];
      if !CAppMessageIsValid(a.request) || !EndPointIsValidIPV4(a.client) {
        assert !CRequestIsValid(a);
        assert !CRequestBatchIsValid(c);
        b := false;
        return;
      }
      pos := pos + 1;
    }

    b := true;
  }

  method DetermineIfValidReplyCache(m:CReplyCache) returns (b:bool)
    requires CReplyCacheIsAbstractable(m)
    requires CReplyCacheIs64Bit(m)
    ensures  b == CReplyCacheIsValid(m)
  {
    b := (|m| as uint64) < 256; // RequestBatchSizeLimit

    assert CReplyCacheIsAbstractable(m);
    forall e | e in m
      ensures CReplyIsValid(m[e])
    {
      assert EndPointIsValidIPV4(e);
      assert CReplyIsAbstractable(m[e]);
    }
    // assert |m| < 256;
    // assert |m| < 0xffff_ffff_ffff_ffff;
    // assert forall rep :: rep in m ==> CReplyIsValid(m[rep]);
  }

  method DetermineIfMessageMarshallable(msg:CMessage) returns (b:bool)
    requires CMessageIsAbstractable(msg)
    requires CMessageIs64Bit(msg)
    ensures  b == Marshallable(msg)
  {
    if msg.CMessage_Invalid? {
      b := false;
    }
    else if msg.CMessage_Request? {
      b := CAppMessageIsValid(msg.val);
    }
    else if msg.CMessage_1a? {
      b := true;
    }
    else if msg.CMessage_1b? {
      b := DetermineIfValidVotes(msg.votes);
    }
    else if msg.CMessage_1c? {
      b := (|msg.val_1c| as uint64) <= RequestBatchSizeLimit() as uint64; // RequestBatchSizeLimit()
    }
    else if msg.CMessage_2av? {
      b := (|msg.val_2av| as uint64) <= RequestBatchSizeLimit() as uint64; // RequestBatchSizeLimit()
    }
    else if msg.CMessage_2b? {
      b := (|msg.val_2b| as uint64) <= RequestBatchSizeLimit() as uint64; // RequestBatchSizeLimit()
    }
    else if msg.CMessage_Heartbeat? {
      b := true;
    }
    else if msg.CMessage_Reply? {
      b := CAppMessageIsValid(msg.reply);
    }
    // else if msg.CMessage_AppStateRequest? {
    //   b := true;
    // }
    // else if msg.CMessage_AppStateSupply? {
    //   var b1 := AppStateMarshallable(msg.app_state);
    //   var b2 := DetermineIfValidReplyCache(msg.reply_cache);
    //   b := b1 && b2;
    // }
    else if msg.CMessage_StartingPhase2? {
      b := true;
    }
    else {
      assert false;
    }
  }

  ////////////////////////////////////////////////////////////////////
  //    Marshalling
  ////////////////////////////////////////////////////////////////////

  method MarshallEndPoint(c:EndPoint) returns (val:V)
    requires EndPointIsValidIPV4(c)
    ensures  ValInGrammar(val, EndPoint_grammar())
    ensures  ValidVal(val)
    ensures  parse_EndPoint(val) == c
  {
    // val := VByteArray(c.public_key);
    val := VUint64(ConvertEndPointToUint64(c));
    lemma_Uint64EndPointRelationships();
  }

  predicate method RequestInRange(c:CRequest)
  {
    && Uint64InRange(c.seqno)
  }

  method MarshallRequest(c:CRequest) returns (val:V)
    requires CRequestIsValid(c)
    ensures  ValInGrammar(val, CRequest_grammar())
    ensures  ValidVal(val)
    ensures  parse_Request(val) == c
  {
    var marshalled_app_message := MarshallCAppMessage(c.request);
    var marshalled_ep := MarshallEndPoint(c.client);
    var seqno := 0;
    if 0 <= c.seqno < 0x10000000000000000 {
      seqno := c.seqno as uint64;
    } else {
      seqno := 0xffff_ffff_ffff_ffff;
      print "Marshall CRequest seqno overflow\n";
    }
    val := VTuple([marshalled_ep, VUint64(seqno), marshalled_app_message]);
    // val := VTuple([marshalled_ep, VUint64(c.seqno), marshalled_app_message, VUint64(c.rtime), VUint64(c.ntime), VUint64(c.atime), VUint64(c.ltime)]);

    assert ValInGrammar(val.t[0], CRequest_grammar().t[0]);      // OBSERVE
    assert ValInGrammar(val.t[1], CRequest_grammar().t[1]);      // OBSERVE
    assert ValInGrammar(val.t[2], CRequest_grammar().t[2]);      // OBSERVE
    calc {
      ValidVal(val);
      ValidVal(val.t[0]) && ValidVal(val.t[1]) && ValidVal(val.t[2]);
    }
    lemma_parserequest(c,val);
  }

  lemma {:axiom} lemma_parserequest(c:CRequest, val:V)
    requires CRequestIsValid(c)
    ensures  ValInGrammar(val, CRequest_grammar())
    ensures  ValidVal(val)
    ensures parse_Request(val) == c

  method MarshallRequestBatch(c:CRequestBatch) returns (val:V)
    requires CRequestBatchIsValid(c)
    ensures  ValInGrammar(val, CRequestBatch_grammar())
    ensures  ValidVal(val)
    ensures  parse_RequestBatch(val) == c
  {
    var reqs := new V[|c| as uint64];

    var i:uint64 := 0;
    while i < |c| as uint64
      invariant 0 <= i as int <= |c|
      invariant forall j :: 0 <= j < i ==> ValInGrammar(reqs[j], CRequest_grammar())
      invariant forall j :: 0 <= j < i ==> ValidVal(reqs[j])
      invariant forall j :: 0 <= j < i ==> parse_Request(reqs[j]) == c[j]
    {
      var single := MarshallRequest(c[i]);
      assert ValInGrammar(single, CRequest_grammar());
      reqs[i] := single;
      i := i + 1;
    }

    val := VArray(reqs[..]);
  }

  predicate method ReplyInRange(c:CReply)
  {
    && Uint64InRange(c.seqno)
  }

  method MarshallReply(c:CReply) returns (val:V)
    requires CReplyIsValid(c)
    ensures  ValInGrammar(val, CReply_grammar())
    ensures  ValidVal(val)
    ensures  ReplyInRange(c) ==> parse_Reply(val) == c
  {
    var marshalled_app_message := MarshallCAppMessage(c.reply);
    var marshalled_ep := MarshallEndPoint(c.client);
    var seqno := 0;
    if 0 <= c.seqno < 0x10000000000000000 {
      seqno := c.seqno as uint64;
    } else {
      seqno := 0xffff_ffff_ffff_ffff;
      print "Marshall CReply seqno overflow\n";
    }
    val := VTuple([marshalled_ep, VUint64(seqno), marshalled_app_message]);
    assert ValInGrammar(val.t[0], CReply_grammar().t[0]);      // OBSERVE
    assert ValInGrammar(val.t[1], CReply_grammar().t[1]);      // OBSERVE
    assert ValInGrammar(val.t[2], CReply_grammar().t[2]);      // OBSERVE
    calc {
      ValidVal(val);
      ValidVal(val.t[0]) && ValidVal(val.t[1]) && ValidVal(val.t[2]);
    }
  }


  predicate method BallotInRange(c:CBallot)
  {
    && Uint64InRange(c.seqno)
    && Uint64InRange(c.proposer_id)
  }
  method MarshallBallot(c:CBallot) returns (val:V)
    ensures  ValInGrammar(val, CBallot_grammar())
    ensures  ValidVal(val)
    ensures  BallotInRange(c) ==> parse_Ballot(val) == c
  {
    var seqno := 0;
    if 0 <= c.seqno < 0x10000000000000000 {
      seqno := c.seqno as uint64;
    } else {
      seqno := 0xffff_ffff_ffff_ffff;
      print "Marshall CBallot seqno overflow\n";
    }
    var id := 0;
    if 0 <= c.proposer_id < 0x10000000000000000 {
      id := c.proposer_id as uint64;
    } else {
      id := 0xffff_ffff_ffff_ffff;
      print "Marshall CBallot seqno overflow\n";
    }
    val := VTuple([VUint64(seqno), VUint64(id)]);
    // assert parse_Ballot(val) == c;
    assert 0 <= c.seqno < 0x10000000000000000 && 0 <= c.proposer_id < 0x10000000000000000 ==> parse_Ballot(val) == c;
  }

  method MarshallOperationNumber(c:COperationNumber) returns (val:V)
    ensures  Uint64InRange(c) ==> ValInGrammar(val, COperationNumber_grammar())
    ensures  Uint64InRange(c) ==>ValidVal(val)
    ensures  Uint64InRange(c) ==> parse_OperationNumber(val) == c
  {
    var opn := 0;
    if 0 <= c < 0x10000000000000000 {
      opn := c as uint64;
    } else {
      opn := 0xffff_ffff_ffff_ffff;
      print "Marshall CRequest seqno overflow\n";
    }
    val := VUint64(opn);
  }

  predicate method VoteInRange(c:CVote)
  {
    && BallotInRange(c.max_value_bal)
  }

  method MarshallVote(c:CVote) returns (val:V)
    requires CVoteIsValid(c)
    ensures  ValInGrammar(val, CVote_grammar())
    ensures  ValidVal(val)
    // ensures  parse_Vote(val) == c
  {
    var bal := MarshallBallot(c.max_value_bal);
    var v := MarshallRequestBatch(c.max_val);
    val := VTuple([bal, v]);
  }

  predicate method Uint64InRange(i:int)
  {
    0 <= i < 0xffff_ffff_ffff_ffff
  }

  predicate method VotesInRange(c:CVotes)
  {
    && (forall i :: i in c ==> Uint64InRange(i) && VoteInRange(c[i]))
  }

  method{:timeLimitMultiplier 3} MarshallVotes(c:CVotes) returns (val:V)
    requires CVotesIsValid(c)
    decreases |c|
    ensures  VotesInRange(c) ==> ValInGrammar(val, CVotes_grammar())
    ensures  VotesInRange(c) ==> |val.a| == |c|
    ensures  VotesInRange(c) ==> ValidVal(val)
    ensures  VotesInRange(c) ==> parse_Votes(val) == c
    //ensures  val == fun_MarshallVotes(c)
    ensures VotesInRange(c) ==> SeqSum(val.a) <= |c| * (8 + (8 + 8) + (8 + (16 + max_val_len())*RequestBatchSizeLimit()))
  {
    if VotesInRange(c) {
      if |c| == 0 {
        val := VArray([]);
        reveal SeqSum();
      } else {
        lemma_non_empty_map_has_elements(c);
        var op :| op in c;
        var marshalled_op := MarshallOperationNumber(op);
        var marshalled_vote := MarshallVote(c[op]);
        var remainder := RemoveElt(c, op);
        var marshalled_remainder := MarshallVotes((remainder));
        assert VotesInRange(c) ==> parse_Votes(marshalled_remainder) == (remainder);
        val := VArray([VTuple([marshalled_op, marshalled_vote])] + marshalled_remainder.a);

        // OBSERVE (everything below; not sure which bit is critical to proving the final ensures
        ghost var tuple := val.a[0];
        ghost var rest := val.a[1..];
        assert ValInGrammar(tuple, CVotes_grammar().elt);
        assert ValInGrammar(tuple.t[0], CVotes_grammar().elt.t[0]);
        assert ValInGrammar(tuple.t[1], CVotes_grammar().elt.t[1]);
        ghost var op' := parse_OperationNumber(tuple.t[0]);
        ghost var vote' := parse_Vote(tuple.t[1]);
        ghost var others' := parse_Votes(VArray(val.a[1..]));
        ghost var m' := others'[op' := vote'];
        assert op' == op;
        // assert vote' == c.v[op];
        // assert others' == CVotes(remainder);
        // assert m' == c.v;
        lemma_MarshallVotes(c, val);

        // Prove the SeqSum ensure
        calc {
          SeqSum(val.a);
             { reveal SeqSum(); }
          SizeOfV(val.a[0]) + SeqSum(val.a[1..]);
        <=
          SizeOfV(val.a[0]) + |remainder| * (8 + (8 + 8) + (8 + ((16 + max_val_len())*RequestBatchSizeLimit())));
          //SizeOfV(val.a[0]) + |remainder| * (8 + (8 + 8) + (24 + max_val_len()));
             { lemma_SeqSum2(val.a[0]); }
          SizeOfV(val.a[0].t[0]) + SizeOfV(val.a[0].t[1]) + |remainder| * (8 + (8 + 8) + (8 + ((16 + max_val_len())*RequestBatchSizeLimit())));
        <=   { lemma_VoteValValid(c[op], val.a[0].t[1]); lemma_VoteBound(c[op], val.a[0].t[1]); }
          8 + (8 + 8) + 8 + ((16 + max_val_len())*|val.a[0].t[1].t[1].a|) + |remainder| * (8 + (8 + 8) + (8 + ((16 + max_val_len())*RequestBatchSizeLimit())));
        <= { assert |val.a[0].t[1].t[1].a| <= RequestBatchSizeLimit(); lemma_mul_upper_bound(16 + max_val_len(), 16 + max_val_len(), |val.a[0].t[1].t[1].a|, RequestBatchSizeLimit());}
          8 + (8 + 8) + 8 + ((16 + max_val_len())*RequestBatchSizeLimit()) + |remainder| * (8 + (8 + 8) + (8 + ((16 + max_val_len())*RequestBatchSizeLimit())));
          1*(8 + (8 + 8) + (8 + ((16 + max_val_len())*RequestBatchSizeLimit()))) + |remainder| * (8 + (8 + 8) + (8 + ((16 + max_val_len())*RequestBatchSizeLimit())));
             { lemma_mul_is_distributive((8 + (8 + 8) + (8 + ((16 + max_val_len())*RequestBatchSizeLimit()))), 1, |remainder|); }
          (1+|remainder|) * (8 + (8 + 8) + (8 + ((16 + max_val_len())*RequestBatchSizeLimit())));
          |c| * (8 + (8 + 8) + (8 + ((16 + max_val_len())*RequestBatchSizeLimit())));
        }
      }
    }
    else {
      print "Marshall CVotes overflow\n";
    }
  }

  lemma {:axiom} lemma_MarshallVotes(c:CVotes, val:V)
    requires CVotesIsValid(c)
    ensures  VotesInRange(c) ==> ValInGrammar(val, CVotes_grammar())
    ensures  VotesInRange(c) ==> |val.a| == |c|
    ensures  VotesInRange(c) ==> ValidVal(val)
    ensures  VotesInRange(c) ==> parse_Votes(val) == c

  predicate method MsgRequestInRange(c:CMessage)
    requires c.CMessage_Request?
  {
    && Uint64InRange(c.seqno_req)
  }

  method MarshallMessage_Request(c:CMessage) returns (val:V)
    requires c.CMessage_Request?
    requires Marshallable(c)
    ensures  ValInGrammar(val, CMessage_Request_grammar())
    ensures  ValidVal(val)
    ensures  MsgRequestInRange(c) ==> parse_Message_Request(val) == c
  {
    var v := MarshallCAppMessage(c.val);
    var seqno:uint64 := 0;
    if MsgRequestInRange(c) {
      seqno := c.seqno_req as uint64;
    }
    val := VTuple([VUint64(seqno), v]);
    assert MsgRequestInRange(c) ==> parse_Message_Request(val) == c;
  }

  predicate method Msg1aInRange(c:CMessage)
    requires c.CMessage_1a?
  {
    && BallotInRange(c.bal_1a)
  }

  method MarshallMessage_1a(c:CMessage) returns (val:V)
    requires c.CMessage_1a?
    requires Marshallable(c)
    ensures  ValInGrammar(val, CMessage_1a_grammar())
    ensures  ValidVal(val)
    ensures  Uint64InRange(c.bal_1a.seqno) && Uint64InRange(c.bal_1a.proposer_id) ==> parse_Message_1a(val) == c
  {
    val := MarshallBallot(c.bal_1a);
  }

  predicate method Msg1bInRange(c:CMessage)
    requires c.CMessage_1b?
  {
    && BallotInRange(c.bal_1b)
    && Uint64InRange(c.log_truncation_point)
    && VotesInRange(c.votes)
  }


  method MarshallMessage_1b(c:CMessage) returns (val:V)
    requires c.CMessage_1b?
    requires Marshallable(c)
    ensures  Msg1bInRange(c) ==> ValInGrammar(val, CMessage_1b_grammar())
    ensures  Msg1bInRange(c) ==> ValidVal(val)
    ensures  Msg1bInRange(c) ==> parse_Message_1b(val) == c
    ensures  Msg1bInRange(c) ==> 0 <= SizeOfV(val) < MaxPacketSize() - 8
  {
    if Msg1bInRange(c){
      var bal := MarshallBallot(c.bal_1b);
      var log_truncation_point := MarshallOperationNumber(c.log_truncation_point);
      var votes := MarshallVotes(c.votes);
      val := VTuple([bal, log_truncation_point, votes]);
      // Prove the bound on SizeOfV(val)
      lemma_SeqSum3(val);
      assert ValInGrammar(val.t[0], CBallot_grammar());   // OBSERVE
      lemma_BallotBound(c.bal_1b, val.t[0]);
      assert ValInGrammar(val.t[1], COperationNumber_grammar());    // OBSERVE
      assert ValInGrammar(val.t[2], CVotes_grammar());    // OBSERVE
      calc {
        SizeOfV(val);
        16 + 8 + SizeOfV(val.t[2]);
      <=
        16 + 8 + 8 + (|c.votes| * (8 + (8 + 8) + (8 + (16 + max_val_len())*RequestBatchSizeLimit())));
        32 + (|c.votes| * (32 + (16 + 64) * RequestBatchSizeLimit()));
        32 + (|c.votes| * 80032);
      < { lemma_mul_strict_inequality(|c.votes|, max_votes_len(), 80032); }
        32 + (max_votes_len() * 80032);
      <
        MaxPacketSize() - 8;
      }
    }
    else {
      print "Marshall 1b overflow\n";
    }
  }

  predicate method Msg1cInRange(c:CMessage)
    requires c.CMessage_1c?
  {
    && BallotInRange(c.bal_1c)
    && Uint64InRange(c.opn_1c)
       // && VotesInRange(c.votes)
  }

  method MarshallMessage_1c(c:CMessage) returns (val:V)
    requires c.CMessage_1c?
    requires Marshallable_1c(c)
    ensures  Msg1cInRange(c) ==> ValInGrammar(val, CMessage_1c_grammar())
    ensures  Msg1cInRange(c) ==> ValidVal(val)
    ensures  Msg1cInRange(c) ==> parse_Message_1c(val) == c
  {
    if Msg1cInRange(c){
      var bal := MarshallBallot(c.bal_1c);
      var op := MarshallOperationNumber(c.opn_1c);
      var v := MarshallRequestBatch(c.val_1c);
      val := VTuple([bal, op, v]);
      assert forall u :: u in val.t ==> ValidVal(u);  // OBSERVE
      assert ValInGrammar(bal, CMessage_1c_grammar().t[0]);    // OBSERVE
      assert ValInGrammar(op,  CMessage_1c_grammar().t[1]);    // OBSERVE
      assert ValInGrammar(v, CMessage_1c_grammar().t[2]);    // OBSERVE
      assert ValInGrammar(val, CMessage_1c_grammar());    // OBSERVE
      assert ValidVal(val);
    }
    else {
      print "Marshall 1c overflow\n";
    }
  }

  predicate method Msg2avInRange(c:CMessage)
    requires c.CMessage_2av?
  {
    && BallotInRange(c.bal_2av)
    && Uint64InRange(c.opn_2av)
       // && VotesInRange(c.votes)
  }

  method MarshallMessage_2av(c:CMessage) returns (val:V)
    requires c.CMessage_2av?
    requires Marshallable_2av(c)
    ensures  Msg2avInRange(c) ==> ValInGrammar(val, CMessage_2av_grammar())
    ensures  Msg2avInRange(c) ==> ValidVal(val)
    ensures  Msg2avInRange(c) ==> parse_Message_2av(val) == c
  {
    if Msg2avInRange(c){
      var bal := MarshallBallot(c.bal_2av);
      var op := MarshallOperationNumber(c.opn_2av);
      var v := MarshallRequestBatch(c.val_2av);
      val := VTuple([bal, op, v]);
      assert forall u :: u in val.t ==> ValidVal(u);  // OBSERVE
      assert ValInGrammar(bal, CMessage_2av_grammar().t[0]);    // OBSERVE
      assert ValInGrammar(op,  CMessage_2av_grammar().t[1]);    // OBSERVE
      assert ValInGrammar(v, CMessage_2av_grammar().t[2]);    // OBSERVE
      assert ValInGrammar(val, CMessage_2av_grammar());    // OBSERVE
      assert ValidVal(val);
    }
    else {
      print "Marshall 2av overflow\n";
    }
  }

  predicate method Msg2bInRange(c:CMessage)
    requires c.CMessage_2b?
  {
    && BallotInRange(c.bal_2b)
    && Uint64InRange(c.opn_2b)
       // && VotesInRange(c.votes)
  }

  method MarshallMessage_2b(c:CMessage) returns (val:V)
    requires c.CMessage_2b?
    requires Marshallable_2b(c)
    ensures  Msg2bInRange(c) ==> ValInGrammar(val, CMessage_2b_grammar())
    ensures  Msg2bInRange(c) ==> ValidVal(val)
    ensures  Msg2bInRange(c) ==> parse_Message_2b(val) == c
  {
    if Msg2bInRange(c) {
      var bal := MarshallBallot(c.bal_2b);
      var op := MarshallOperationNumber(c.opn_2b);
      var v := MarshallRequestBatch(c.val_2b);
      val := VTuple([bal, op, v]);
      assert ValInGrammar(bal, CBallot_grammar());    // OBSERVE
      assert ValInGrammar(op, COperationNumber_grammar());    // OBSERVE
      assert ValInGrammar(v, CRequestBatch_grammar());    // OBSERVE
      assert ValInGrammar(val, CMessage_2b_grammar());    // OBSERVE
    }
    else {
      print "Marshall 2b overflow\n";
    }
  }

  predicate method MsgHeartBeatInRange(c:CMessage)
    requires c.CMessage_Heartbeat?
  {
    && BallotInRange(c.bal_heartbeat)
    && Uint64InRange(c.opn_ckpt)
       // && VotesInRange(c.votes)
  }

  method MarshallMessage_Heartbeat(c:CMessage) returns (val:V)
    requires c.CMessage_Heartbeat?
    requires Marshallable(c)
    ensures  MsgHeartBeatInRange(c) ==> ValInGrammar(val, CMessage_Heartbeat_grammar())
    ensures  MsgHeartBeatInRange(c) ==> ValidVal(val)
    ensures  MsgHeartBeatInRange(c) ==> parse_Message_Heartbeat(val) == c
  {
    if MsgHeartBeatInRange(c) {
      var ballot := MarshallBallot(c.bal_heartbeat);
      var op := MarshallOperationNumber(c.opn_ckpt);
      val := VTuple([ballot, VUint64(if c.suspicious then 1 else 0), op]);
      assert parse_Message_Heartbeat(val) == c;
    }
    else {
      print "Marshall heartbeat overflow\n";
    }
  }

  predicate method MsgReplyInRange(c:CMessage)
    requires c.CMessage_Reply?
  {
    // && BallotInRange(c.bal_heartbeat)
    && Uint64InRange(c.seqno_reply)
    // && VotesInRange(c.votes)
  }

  method MarshallMessage_Reply(c:CMessage) returns (val:V)
    requires c.CMessage_Reply?
    requires Marshallable(c)
    ensures  MsgReplyInRange(c) ==> ValInGrammar(val, CMessage_Reply_grammar())
    ensures  MsgReplyInRange(c) ==> ValidVal(val)
    ensures  MsgReplyInRange(c) ==> parse_Message_Reply(val) == c
  {
    if MsgReplyInRange(c) {
      var app_val := MarshallCAppMessage(c.reply);
      var seqno :uint64 := 0;
      if MsgReplyInRange(c) {
        seqno := c.seqno_reply as uint64;
      }
      val := VTuple([VUint64(seqno), app_val]);
      assert parse_Message_Reply(val) == c;
    }
    else {
      print "Marshall reply overflow\n";
    }
  }

  // predicate method MsgAppStateReqInRange(c:CMessage)
  //   requires c.CMessage_AppStateRequest?
  // {
  //   && BallotInRange(c.bal_state_req)
  //   && Uint64InRange(c.opn_state_req)
  //      // && VotesInRange(c.votes)
  // }

  // method MarshallMessage_AppStateRequest(c:CMessage) returns (val:V)
  //   requires c.CMessage_AppStateRequest?
  //   requires Marshallable(c)
  //   ensures  MsgAppStateReqInRange(c) ==> ValInGrammar(val, CMessage_AppStateRequest_grammar())
  //   ensures  MsgAppStateReqInRange(c) ==> ValidVal(val)
  //   ensures  MsgAppStateReqInRange(c) ==> parse_Message_AppStateRequest(val) == c
  // {
  //   if MsgAppStateReqInRange(c) {
  //     var ballot := MarshallBallot(c.bal_state_req);
  //     var opn := MarshallOperationNumber(c.opn_state_req);
  //     val := VTuple([ballot, opn]);
  //   }
  //   else {
  //     print "Marshall appstatereq overflow\n";
  //   }
  // }

  predicate method ReplyCacheInRange(c:CReplyCache)
  {
    && (forall i :: i in c ==> ReplyInRange(c[i]))
  }


  method MarshallReplyCache(c:CReplyCache) returns (val:V)
    requires CReplyCacheIsValid(c)
    decreases |c|
    ensures  ReplyCacheInRange(c) ==> ValInGrammar(val, CReplyCache_grammar())
    ensures  ReplyCacheInRange(c) ==> |val.a| == |c|
    ensures  ReplyCacheInRange(c) ==> ValidVal(val)
    ensures  ReplyCacheInRange(c) ==> parse_ReplyCache(val) == c
    ensures ReplyCacheInRange(c) ==> SeqSum(val.a) <= |c| * (8 + (8 + 8) + (24 + max_val_len()));
  {
    if ReplyCacheInRange(c){
      if |c| == 0 {
        val := VArray([]);
        reveal SeqSum();
      } else {
        //lemma_non_empty_map_has_elements(c);
        var ep :| ep in c;
        var marshalled_ep := MarshallEndPoint(ep);
        var marshalled_reply := MarshallReply(c[ep]);
        var remainder := RemoveElt(c, ep);
        assert forall e :: e in remainder ==> CReplyIsValid(remainder[e]);
        var marshalled_remainder := MarshallReplyCache(remainder);
        assert parse_ReplyCache(marshalled_remainder) == remainder;
        val := VArray([VTuple([marshalled_ep, marshalled_reply])] + marshalled_remainder.a);

        // OBSERVE (everything below; not sure which bit is critical to proving the final ensures
        ghost var tuple := val.a[0];
        ghost var rest := val.a[1..];
        assert ValInGrammar(tuple, CReplyCache_grammar().elt);
        assert ValInGrammar(tuple.t[0], CReplyCache_grammar().elt.t[0]);
        assert ValInGrammar(tuple.t[1], CReplyCache_grammar().elt.t[1]);
        ghost var ep' := parse_EndPoint(tuple.t[0]);
        ghost var reply' := parse_Reply(tuple.t[1]);
        ghost var others' := parse_ReplyCache(VArray(val.a[1..]));
        ghost var m' := others'[ep' := reply'];
        assert ep' == ep;
        assert reply' == c[ep];
        assert others' == remainder;
        assert m' == c;

        // Prove the SeqSum ensure
        calc {
          SeqSum(val.a);
            { reveal SeqSum(); }
          SizeOfV(val.a[0]) + SeqSum(val.a[1..]);
        <=
          SizeOfV(val.a[0]) + |remainder| * (8 + (8 + 8) + (24 + max_val_len()));
          SizeOfV(val.a[0]) + |remainder| * (8 + (8 + 8) + (24 + max_val_len()));
            { lemma_SeqSum2(val.a[0]); }
          SizeOfV(val.a[0].t[0]) + SizeOfV(val.a[0].t[1]) + |remainder| * (8 + (8 + 8) + (24 + max_val_len()));
        <   { lemma_ReplyValValid(c[ep], val.a[0].t[1]); lemma_ReplyBound(c[ep], val.a[0].t[1]); }
          8 + (8 + 8) + (24 + max_val_len()) + |remainder| * (8 + (8 + 8) + (24 + max_val_len()));
          1*(8 + (8 + 8) + (24 + max_val_len())) + |remainder| * (8 + (8 + 8) + (24 + max_val_len()));
            { lemma_mul_is_distributive((8 + (8 + 8) + (24 + max_val_len())), 1, |remainder|); }
          (1+|remainder|) * (8 + (8 + 8) + (24 + max_val_len()));
          |c| * (8 + (8 + 8) + (24 + max_val_len()));
        }
      }
    }
    else {
      print "Marshall replycache overflow\n";
    }
  }


  lemma lemma_ReplyValValid(c:CReply, val:V)
    requires ValInGrammar(val, CReply_grammar())
    requires CReplyIsValid(c)
    requires parse_Reply(val) == c
    ensures ValidVal(val)
  {
    lemma_SeqSum3(val);
    assert ValInGrammar(val.t[0], EndPoint_grammar());    // OBSERVE
    assert ValInGrammar(val.t[1], GUint64);    // OBSERVE
    assert ValInGrammar(val.t[2], CAppMessage_grammar());    // OBSERVE

    // Lots of OBSERVE below
    ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar()]);
    assert ValInGrammar(val, gtuple);
    assert ValInGrammar(val.t[0], gtuple.t[0]);
    assert ValInGrammar(val.t[1], gtuple.t[1]);
    assert ValInGrammar(val.t[2], gtuple.t[2]);
    assert ValidVal(val.t[0]);
    assert ValidVal(val.t[1]);
    lemma_AppMessageBound(c.reply, val.t[2]);
    assert ValidVal(val.t[2]);
  }


  lemma lemma_ReplyBound(c:CReply, val:V)
    requires ValInGrammar(val, CReply_grammar())
    requires CReplyIsValid(c)
    requires parse_Reply(val) == c
    ensures  SizeOfV(val) < 24 + max_val_len()
  {
    ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar()]);
    assert ValInGrammar(val, gtuple);
    lemma_SeqSum3(val);
    lemma_AppMessageBound(c.reply, val.t[2]);
    assert ValInGrammar(val.t[0], gtuple.t[0]);
    assert ValInGrammar(val.t[1], gtuple.t[1]);
    assert SizeOfV(val.t[0]) == 8;
    assert SizeOfV(val.t[1]) == 8;
    assert SizeOfV(val.t[2]) < max_val_len();
  }

  // predicate method MsgAppStateSupplyInRange(c:CMessage)
  //   requires c.CMessage_AppStateSupply?
  // {
  //   && BallotInRange(c.bal_state_supply)
  //   && Uint64InRange(c.opn_state_supply)
  //   && ReplyCacheInRange(c.reply_cache)
  //      // && VotesInRange(c.votes)
  // }

  // method MarshallMessage_AppStateSupply(c:CMessage) returns (val:V)
  //   requires c.CMessage_AppStateSupply?
  //   requires Marshallable(c)
  //   ensures  MsgAppStateSupplyInRange(c) ==> ValInGrammar(val, CMessage_AppStateSupply_grammar())
  //   ensures  MsgAppStateSupplyInRange(c) ==> ValidVal(val)
  //   ensures  MsgAppStateSupplyInRange(c) ==> parse_Message_AppStateSupply(val) == c
  //   ensures  MsgAppStateSupplyInRange(c) ==> 0 <= SizeOfV(val) < MaxPacketSize() - 8
  // {
  //   if MsgAppStateSupplyInRange(c) {
  //     var ballot := MarshallBallot(c.bal_state_supply);
  //     var opn_state_supply := MarshallOperationNumber(c.opn_state_supply);
  //     var app_state := MarshallAppState(c.app_state);
  //     var reply_cache := MarshallReplyCache(c.reply_cache);
  //     val := VTuple([ballot, opn_state_supply, app_state, reply_cache]);

  //     // Prove the bound on SizeOfV(val)
  //     lemma_SeqSum4(val);
  //     assert ValInGrammar(val.t[0], CBallot_grammar());   // OBSERVE
  //     lemma_BallotBound(c.bal_state_supply, val.t[0]);
  //     assert ValInGrammar(val.t[1], COperationNumber_grammar());   // OBSERVE
  //     assert ValInGrammar(val.t[2], CAppState_grammar());    // OBSERVE
  //     lemma_AppStateBound(c.app_state, val.t[2]);
  //     assert ValInGrammar(val.t[3], CReplyCache_grammar());    // OBSERVE
  //     calc {
  //       SizeOfV(val);
  //       SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]);
  //     <
  //       16 + 16 + max_app_state_size() + SizeOfV(val.t[3]);
  //     <=
  //       16 + 16 + max_app_state_size() + (8 + |c.reply_cache| * (8 + (8 + 8) + (24 + max_val_len())));
  //       16 + 16 + max_app_state_size() + (8 + |c.reply_cache| * (8 + (8 + 8) + (24 + 64)));
  //       16 + 16 + max_app_state_size() + (8 + |c.reply_cache| * 112);
  //       40 + max_app_state_size() + |c.reply_cache| * 112;
  //       40 + 0x8000 + |c.reply_cache| * 112;
  //     < { lemma_mul_strict_inequality(|c.reply_cache|, max_reply_cache_size(), 112); }
  //       40 + 0x8000 + max_reply_cache_size() * 112;
  //     <
  //       MaxPacketSize() - 8;
  //     }
  //   }
  //   else {
  //     print "Marshall appstatesupply overflow\n";
  //   }
  // }


  lemma lemma_SeqSum4(val:V)
    requires val.VTuple?
    requires |val.t| == 4
    ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3])
  {
    calc {
      SeqSum(val.t);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum(val.t[3..]);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SeqSum(val.t[4..]);
      { assert val.t[4..] == []; }        // OBSERVE
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SeqSum([]);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]);
    }
  }

  predicate method MsgStartPhase2InRange(c:CMessage)
    requires c.CMessage_StartingPhase2?
  {
    && BallotInRange(c.bal_2)
    && Uint64InRange(c.logTruncationPoint_2)
  }

  method MarshallMessage_StartingPhase2(c:CMessage) returns (val:V)
    requires c.CMessage_StartingPhase2?
    requires Marshallable(c)
    ensures  MsgStartPhase2InRange(c) ==> ValInGrammar(val, CMessage_StartingPhase2_grammar())
    ensures  MsgStartPhase2InRange(c) ==> ValidVal(val)
    ensures  MsgStartPhase2InRange(c) ==> parse_Message_StartingPhase2(val) == c
  {
    if MsgStartPhase2InRange(c) {
      var bal := MarshallBallot(c.bal_2);
      var op := MarshallOperationNumber(c.logTruncationPoint_2);
      val := VTuple([bal, op]);
    }
    else {
      print "Marshall startphase2 overflow\n";
    }
  }

  predicate method MsgInRange(c:CMessage)
  {
    if c.CMessage_Request? then
      MsgRequestInRange(c)
    else if c.CMessage_1a? then
      Msg1aInRange(c)
    else if c.CMessage_1b? then
      Msg1bInRange(c)
    else if c.CMessage_1c? then
      Msg1cInRange(c)
    else if c.CMessage_2av? then
      Msg2avInRange(c)
    else if c.CMessage_2b? then
      Msg2bInRange(c)
    else if c.CMessage_Heartbeat? then
      MsgHeartBeatInRange(c)
    else if c.CMessage_Reply? then
      MsgReplyInRange(c)
    // else if c.CMessage_AppStateRequest? then
    //   MsgAppStateReqInRange(c)
    // else if c.CMessage_AppStateSupply? then
    //   MsgAppStateSupplyInRange(c)
    else if c.CMessage_StartingPhase2? then
      MsgStartPhase2InRange(c)
    else
      true
  }

  // predicate method MsgInRange(c:CMessage)
  // {
  //   match c
  //     case CMessage_Invalid => true
  //     case CMessage_Request => MsgRequestInRange(c)
  //     case CMessage_1a => Msg1aInRange(c)
  //     case CMessage_1b => Msg1bInRange(c)
  //     case CMessage_2a => Msg2aInRange(c)
  //     case CMessage_2b => Msg2bInRange(c)
  //     case CMessage_Heartbeat => MsgHeartBeatInRange(c)
  //     case CMessage_Reply => MsgReplyInRange(c)
  //     case CMessage_AppStateRequest => MsgAppStateReqInRange(c)
  //     case CMessage_AppStateSupply => MsgAppStateSupplyInRange(c)
  //     case CMessage_StartingPhase2 => MsgStartPhase2InRange(c)
  // }

  method {:timeLimitMultiplier 2} MarshallMessage(c:CMessage) returns (val:V)
    requires Marshallable(c)
    ensures  MsgInRange(c) ==> ValInGrammar(val, CMessage_grammar())
    ensures  MsgInRange(c) ==> ValidVal(val)
    ensures  MsgInRange(c) ==> parse_Message(val) == c
    ensures  MsgInRange(c) ==> c.CMessage_1b? ==> 0 <= SizeOfV(val) < MaxPacketSize()
    // ensures  MsgInRange(c) ==> c.CMessage_AppStateSupply? ==> 0 <= SizeOfV(val) < MaxPacketSize()
  {
    if MsgInRange(c) {
      // var start_time := Time.GetDebugTimeTicks();
      assert !c.CMessage_Invalid?;
      if c.CMessage_Request? {
        var msg := MarshallMessage_Request(c);
        val := VCase(0, msg);
        // var end_time := Time.GetDebugTimeTicks();
        // RecordTimingSeq("MarshallMessage_Request", start_time, end_time);
      } else if c.CMessage_1a? {
        var msg := MarshallMessage_1a(c);
        val := VCase(1, msg);
        // var end_time := Time.GetDebugTimeTicks();
        // RecordTimingSeq("MarshallMessage_1a", start_time, end_time);
      } else if c.CMessage_1b? {
        var msg := MarshallMessage_1b(c);
        val := VCase(2, msg);
        // var end_time := Time.GetDebugTimeTicks();
        // RecordTimingSeq("MarshallMessage_1b", start_time, end_time);
      } else if c.CMessage_1c? {
        var msg := MarshallMessage_1c(c);
        val := VCase(3, msg);
        // var end_time := Time.GetDebugTimeTicks();
        // RecordTimingSeq("MarshallMessage_1c", start_time, end_time);
      } else if c.CMessage_2av? {
        var msg := MarshallMessage_2av(c);
        val := VCase(4, msg);
        // var end_time := Time.GetDebugTimeTicks();
        // RecordTimingSeq("MarshallMessage_2av", start_time, end_time);
      } else if c.CMessage_2b? {
        var msg := MarshallMessage_2b(c);
        val := VCase(5, msg);
        // var end_time := Time.GetDebugTimeTicks();
        // RecordTimingSeq("MarshallMessage_2b", start_time, end_time);
      } else if c.CMessage_Heartbeat? {
        var msg := MarshallMessage_Heartbeat(c);
        val := VCase(6, msg);
        // var end_time := Time.GetDebugTimeTicks();
        // RecordTimingSeq("MarshallMessage_Heartbeat", start_time, end_time);
      } else if c.CMessage_Reply? {
        var msg := MarshallMessage_Reply(c);
        val := VCase(7, msg);
        assert CMessage_grammar().cases[7] == CMessage_Reply_grammar();
        // var end_time := Time.GetDebugTimeTicks();
        // RecordTimingSeq("MarshallMessage_Reply", start_time, end_time);
      } 
      // else if c.CMessage_AppStateRequest? {
      //   var msg := MarshallMessage_AppStateRequest(c);
      //   val := VCase(8, msg);
      //   // var end_time := Time.GetDebugTimeTicks();
      //   // RecordTimingSeq("MarshallMessage_AppStateRequest", start_time, end_time);
      // } else if c.CMessage_AppStateSupply? {
      //   var msg := MarshallMessage_AppStateSupply(c);
      //   val := VCase(9, msg);
      //   // var end_time := Time.GetDebugTimeTicks();
      //   // RecordTimingSeq("MarshallMessage_AppStateSupply", start_time, end_time);
      // } 
      else if c.CMessage_StartingPhase2? {
        var msg := MarshallMessage_StartingPhase2(c);
        val := VCase(8, msg);
        // var end_time := Time.GetDebugTimeTicks();
        // RecordTimingSeq("MarshallMessage_StartingPhase2", start_time, end_time);
      }

      // The following should work just as well as above, but it doesn't.  Not sure why.
      //    var msg:V;
      //    match c
      //      case CMessage_Request(_,_) => msg := MarshallMessage_Request(c);
      //      case CMessage_1a(_)        => msg := MarshallMessage_1a(c);  assert ValInGrammar(msg, CMessage_1a_grammar());
      //      case CMessage_1b(_,_)      => msg := MarshallMessage_1b(c);
      //      case CMessage_2a(_,_,_)    => msg := MarshallMessage_2a(c);
      //      case CMessage_2b(_,_,_)    => msg := MarshallMessage_2b(c);
      //      case CMessage_Decision(_,_)=> msg := MarshallMessage_Decision(c);
      //    
      //    assert CMessage_grammar().cases[1] == CMessage_1a_grammar();
      //
      //    match c
      //      case CMessage_Request(_,_) => val := VCase(0, msg);
      //      case CMessage_1a(_)        => val := VCase(1, msg);
      //      case CMessage_1b(_,_)      => val := VCase(2, msg);
      //      case CMessage_2a(_,_,_)    => val := VCase(3, msg);
      //      case CMessage_2b(_,_,_)    => val := VCase(4, msg);
      //      case CMessage_Decision(_,_)=> val := VCase(5, msg);
      //    }
    }
  }

  lemma lemma_SeqSum2(val:V)
    requires val.VTuple?
    requires |val.t| == 2
    ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1])
  {
    calc {
      SeqSum(val.t);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
      { assert val.t[2..] == []; }        // OBSERVE
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum([]);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]);
    }
  }

  lemma lemma_SeqSum3(val:V)
    requires val.VTuple?
    requires |val.t| == 3
    ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2])
  {
    calc {
      SeqSum(val.t);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum(val.t[3..]);
      { assert val.t[3..] == []; }        // OBSERVE
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum([]);
      { reveal SeqSum(); }
      SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]);
    }
  }

  // lemma lemma_SeqSum4(val:V)
  //   requires val.VTuple?
  //   requires |val.t| == 4
  //   ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3])
  // {
  //   calc {
  //     SeqSum(val.t);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum(val.t[3..]);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SeqSum(val.t[4..]);
  //       { assert val.t[4..] == []; }        // OBSERVE
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SeqSum([]);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]);
  //   }
  // }


  // lemma lemma_SeqSum4(val:V)
  //   requires val.VTuple?
  //   requires |val.t| == 4
  //   ensures  SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3])
  // {
  //   calc {
  //     SeqSum(val.t);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SeqSum(val.t[1..]);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SeqSum(val.t[2..]);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SeqSum(val.t[3..]);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SeqSum(val.t[4..]);
  //       { assert val.t[4..] == []; }        // OBSERVE
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SeqSum([]);
  //       { reveal SeqSum(); }
  //     SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]);
  //   }
  // }

  lemma {:axiom} lemma_SeqSum5(val:V)
    requires val.VTuple?
    requires |val.t| == 5
    ensures SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SizeOfV(val.t[4])

  lemma {:axiom} lemma_SeqSum7(val:V)
    requires val.VTuple?
    requires |val.t| == 7
    ensures SizeOfV(val) == SizeOfV(val.t[0]) + SizeOfV(val.t[1]) + SizeOfV(val.t[2]) + SizeOfV(val.t[3]) + SizeOfV(val.t[4]) + SizeOfV(val.t[5]) + SizeOfV(val.t[6])

  lemma lemma_BallotBound(c:CBallot, val:V)
    requires ValInGrammar(val, CBallot_grammar())
    requires ValidVal(val)
    requires parse_Ballot(val) == c
    ensures  SizeOfV(val) == 16
  {
    assert |val.t| == |CBallot_grammar().t| == 2;
    assert ValInGrammar(val.t[0], GUint64);
    assert ValInGrammar(val.t[1], GUint64);
    lemma_SeqSum2(val);
    assert SeqSum(val.t) == 16;
  }

  lemma lemma_CRequestBound(c:CRequest, val:V)
    requires ValInGrammar(val, CRequest_grammar())
    requires CRequestIsValid(c)
    requires parse_Request(val) == c
    ensures  SizeOfV(val) < 16 + max_val_len()
  {
    // ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar(), GUint64, GUint64, GUint64, GUint64]);
    ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar()]);
    assert ValInGrammar(val, gtuple);

    // lemma_SeqSum7(val);
    lemma_SeqSum3(val);
    lemma_AppMessageBound(c.request, val.t[2]);
    assert ValInGrammar(val.t[0], gtuple.t[0]);
    assert ValInGrammar(val.t[1], gtuple.t[1]);
    assert SizeOfV(val.t[0]) == 8;
    assert SizeOfV(val.t[1]) == 8;
    //assert SizeOfV(val.t[2]) < max_val_len();
    lemma_CRequestBoundSize(c,val);
  }

  lemma {:axiom} lemma_CRequestBoundSize(c:CRequest, val:V)
    requires ValInGrammar(val, CRequest_grammar())
    requires CRequestIsValid(c)
    requires parse_Request(val) == c
    ensures  SizeOfV(val) < 16 + max_val_len()

  lemma lemma_CRequestBatchBound(c:CRequestBatch, val:V)
    requires ValInGrammar(val, CRequestBatch_grammar())
    requires CRequestBatchIsValid(c)
    requires parse_RequestBatch(val) == c
    decreases |c|
    ensures  SeqSum(val.a) <= (16 + max_val_len())*|val.a|
  {
    //ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar()]);
    ghost var garray := GArray(CRequest_grammar());
    assert ValInGrammar(val, garray);
    reveal SeqSum();
    if |val.a| == 0 {
      assert SeqSum(val.a) <= (16 + max_val_len())*|val.a|;
    } else {
      var req := parse_Request(val.a[0]);
      var restVal:V := VArray(val.a[1..]);
      var rest := parse_RequestBatch(restVal);
      assert c == [req] + rest;
      var x := 16 + max_val_len();
      var N := |val.a|;
      lemma_CRequestBatchBound(rest, restVal);
      assert SeqSum(val.a[1..]) <= (x)*(N-1);
      lemma_CRequestBound(req, val.a[0]);
      assert SizeOfV(val.a[0]) < x;
      assert SeqSum(val.a) == SizeOfV(val.a[0]) + SeqSum(val.a[1..]);
      assert |val.a| == |val.a[1..]| + 1;
      lemma_mul_is_distributive(x, N-1, 1);
      assert SeqSum(val.a) <= (x)*N;
    }
  }

  // lemma lemma_ReplyBound(c:CReply, val:V)
  //   requires ValInGrammar(val, CReply_grammar())
  //   requires ValidReply(c)
  //   requires parse_Reply(val) == c
  //   ensures  SizeOfV(val) <= 0x10_0018 + MaxAppRequestSize()
  // {
  //   ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, GByteArray]);
  //   assert ValInGrammar(val, gtuple);
  //   lemma_SeqSum3(val);
  //   assert ValInGrammar(val.t[0], gtuple.t[0]);
  //   assert ValInGrammar(val.t[1], gtuple.t[1]);
  //   assert SizeOfV(val.t[0]) <= 0x10_0008;
  //   assert SizeOfV(val.t[1]) == 8;
  //   assert SizeOfV(val.t[2]) <= 8 + MaxAppRequestSize();
  // }

  // lemma lemma_ReplyValValid(c:CReply, val:V)
  //   requires ValInGrammar(val, CReply_grammar())
  //   requires ValidReply(c)
  //   requires parse_Reply(val) == c
  //   ensures ValidVal(val)
  // {
  //   lemma_SeqSum3(val);
  //   assert ValInGrammar(val.t[0], EndPoint_grammar());    // OBSERVE
  //   assert ValInGrammar(val.t[1], GUint64);    // OBSERVE
  //   assert ValInGrammar(val.t[2], GByteArray);    // OBSERVE

  //   // Lots of OBSERVE below
  //   ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, GByteArray]);
  //   assert ValInGrammar(val, gtuple);
  //   assert ValInGrammar(val.t[0], gtuple.t[0]);
  //   assert ValInGrammar(val.t[1], gtuple.t[1]);
  //   assert ValInGrammar(val.t[2], gtuple.t[2]);
  //   assert ValidVal(val.t[0]);
  //   assert ValidVal(val.t[1]);
  //   assert ValidVal(val.t[2]);
  // }

  lemma {:axiom} lemma_MsgMarshallable(m:CMessage)
    ensures Marshallable(m)

  lemma {:timeLimitMultiplier 2} lemma_VoteValValid(c:CVote, val:V)
    requires ValInGrammar(val, CVote_grammar())
    requires CVoteIsValid(c)
    requires parse_Vote(val) == c
    ensures ValidVal(val)
  {
    lemma_SeqSum2(val);
    assert ValInGrammar(val.t[0], CBallot_grammar());    // OBSERVE
    assert ValInGrammar(val.t[1], CRequestBatch_grammar());    // OBSERVE
    lemma_BallotBound(c.max_value_bal, val.t[0]);
    lemma_CRequestBatchBound(c.max_val, val.t[1]);

    ghost var garray := GArray(CRequest_grammar());
    assert ValInGrammar(val.t[1], garray);
    // ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar(), GUint64, GUint64, GUint64, GUint64]);
    ghost var gtuple := GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar()]);
    forall i, v | 0 <= i < |val.t[1].a|&& v == val.t[1].a[i]
      ensures ValidVal(v)
    {
      assert ValInGrammar(v, gtuple);
      assert ValInGrammar(v.t[0], gtuple.t[0]);
      assert ValInGrammar(v.t[1], gtuple.t[1]);
      assert ValInGrammar(v.t[2], gtuple.t[2]);
      assert ValidVal(v.t[0]);
      assert ValidVal(v.t[1]);
      lemma_AppMessageBound(c.max_val[i].request, v.t[2]);
      assert ValidVal(v.t[2]);
      assert ValidVal(v);
    }
    assert |val.t[1].a| == |c.max_val|;
    assert CVoteIsValid(c);
    assert CRequestBatchIsValid(c.max_val);
    assert |c.max_val| < 0x1_0000_0000;
    assert |val.t[1].a| < 0x1_0000_0000_0000_0000;
    assert forall v :: v in val.t[1].a ==> ValidVal(v);

    calc ==> {
      true;
      ValidVal(val.t[0]);
      ValidVal(val.t[0]) && ValidVal(val.t[1]);
      ValidVal(val);
    }
  }

  lemma lemma_VoteBound(c:CVote, val:V)
    requires ValInGrammar(val, CVote_grammar())
    requires ValInGrammar(val.t[1], CRequestBatch_grammar())
    requires ValidVal(val)
    requires CVoteIsValid(c)
    requires parse_Vote(val) == c
    ensures  SizeOfV(val) <= (8 + 8) + 8 + ((16 + max_val_len())*|val.t[1].a|)
  {
    lemma_SeqSum2(val);
    assert ValInGrammar(val.t[0], CBallot_grammar());    // OBSERVE
    assert ValInGrammar(val.t[1], CRequestBatch_grammar());    // OBSERVE

    lemma_BallotBound(c.max_value_bal, val.t[0]);
    lemma_CRequestBatchBound(c.max_val, val.t[1]);
  }

  lemma lemma_MarshallableBound(c:CMessage, val:V)
    requires Marshallable(c)
    requires ValInGrammar(val, CMessage_grammar())
    requires ValidVal(val)
    requires parse_Message(val) == c
    // ensures  !c.CMessage_1b? && !c.CMessage_AppStateSupply? ==> 0 <= SizeOfV(val) < MaxPacketSize()
  {
    assert !c.CMessage_Invalid?;
    if c.CMessage_Request? {
      lemma_SeqSum2(val.val);
      assert ValInGrammar(val.val.t[0], GUint64);             // OBSERVE
      assert ValInGrammar(val.val.t[1], CAppMessage_grammar());    // OBSERVE
      lemma_AppMessageBound(c.val, val.val.t[1]);
    } else if c.CMessage_1a? {
      assert ValInGrammar(val.val, CMessage_1a_grammar());    // OBSERVE
      assert ValInGrammar(val.val, CBallot_grammar());        // OBSERVE
      lemma_BallotBound(c.bal_1a, val.val);
      assert SizeOfV(val) == 24;
      /*  We prove this case during marshalling
        } else if c.CMessage_1b? {
      */
    } else if c.CMessage_1c? {
      lemma_SeqSum3(val.val);
      lemma_BallotBound(c.bal_1c, val.val.t[0]);
      assert SizeOfV(val.val.t[0]) == 16;
      assert ValInGrammar(val.val.t[1], GUint64);             // OBSERVE
      assert SizeOfV(val.val.t[1]) == 8;
      assert ValInGrammar(val.val.t[2], CRequestBatch_grammar());    // OBSERVE
      //assert SizeOfV(val.val.t[2]) == 8 + |val.val.t[2].b| == 8 + |c.val_1c.v|;
      lemma_CRequestBatchBound(c.val_1c, val.val.t[2]);
      assert |val.val.t[2].a| == |c.val_1c|;

      calc {
        SizeOfV(val.val.t[2]);
        8 + SeqSum(val.val.t[2].a);
      <=
        8 + (16 + max_val_len())*|val.val.t[2].a|;
        8 + (16 + 64)*|val.val.t[2].a|;
      <
        MaxPacketSize();
      }
      assert 0 <= SizeOfV(val.val.t[2]) < MaxPacketSize();
      assert 0 <= SizeOfV(val.val) < MaxPacketSize();
      assert 0 <= SizeOfV(val) < MaxPacketSize();
    } else if c.CMessage_2av? {
      lemma_SeqSum3(val.val);
      lemma_BallotBound(c.bal_2av, val.val.t[0]);
      assert SizeOfV(val.val.t[0]) == 16;
      assert ValInGrammar(val.val.t[1], GUint64);             // OBSERVE
      assert SizeOfV(val.val.t[1]) == 8;
      assert ValInGrammar(val.val.t[2], CRequestBatch_grammar());    // OBSERVE
      //assert SizeOfV(val.val.t[2]) == 8 + |val.val.t[2].b| == 8 + |c.val_2a.v|;
      lemma_CRequestBatchBound(c.val_2av, val.val.t[2]);
      assert |val.val.t[2].a| == |c.val_2av|;

      calc {
        SizeOfV(val.val.t[2]);
        8 + SeqSum(val.val.t[2].a);
      <=
        8 + (16 + max_val_len())*|val.val.t[2].a|;
        8 + (16 + 64)*|val.val.t[2].a|;
      <
        MaxPacketSize();
      }
      assert 0 <= SizeOfV(val.val.t[2]) < MaxPacketSize();
      assert 0 <= SizeOfV(val.val) < MaxPacketSize();
      assert 0 <= SizeOfV(val) < MaxPacketSize();
    } else if c.CMessage_2b? {
      lemma_SeqSum3(val.val);
      lemma_BallotBound(c.bal_2b, val.val.t[0]);
      assert SizeOfV(val.val.t[0]) == 16;
      assert ValInGrammar(val.val.t[1], GUint64);             // OBSERVE
      assert SizeOfV(val.val.t[1]) == 8;
      assert ValInGrammar(val.val.t[2], CRequestBatch_grammar());    // OBSERVE
      //assert SizeOfV(val.val.t[2]) == 8 + |val.val.t[2].b| == 8 + |c.val_2b.v|;
      lemma_CRequestBatchBound(c.val_2b, val.val.t[2]);
    } else if c.CMessage_Heartbeat? {
      lemma_SeqSum3(val.val);
      assert ValInGrammar(val.val.t[0], CBallot_grammar());   // OBSERVE
      assert ValInGrammar(val.val.t[1], GUint64);             // OBSERVE
      assert ValInGrammar(val.val.t[2], COperationNumber_grammar());  // OBSERVE
      lemma_BallotBound(c.bal_heartbeat, val.val.t[0]);
    } else if c.CMessage_Reply? {
      lemma_SeqSum2(val.val);
      assert ValInGrammar(val.val.t[0], GUint64);               // OBSERVE
      assert ValInGrammar(val.val.t[1], CAppMessage_grammar()); // OBSERVE
      lemma_AppMessageBound(c.reply, val.val.t[1]);
    } 
    // else if c.CMessage_AppStateRequest? {
    //   lemma_SeqSum2(val.val);
    //   assert ValInGrammar(val.val.t[0], CBallot_grammar());   // OBSERVE
    //   assert ValInGrammar(val.val.t[1], COperationNumber_grammar());  // OBSERVE
    //   lemma_BallotBound(c.bal_state_req, val.val.t[0]);
    //   assert 0 <= SizeOfV(val) < MaxPacketSize();
    //   // assert SizeOfV(val.val.t[0]) == 8;
    //   /*  We prove this case during marshalling
    //     } else if c.CMessage_AppStateSupply? {
    //   */
    // } 
    else if c.CMessage_StartingPhase2? {
      lemma_SeqSum2(val.val);
      assert ValInGrammar(val.val.t[0], CBallot_grammar());   // OBSERVE
      assert ValInGrammar(val.val.t[1], COperationNumber_grammar());  // OBSERVE
      lemma_BallotBound(c.bal_2, val.val.t[0]);
    }
  }

  ////////////////////////////////////////////////////////////////////////
  // These functions need to be here, rather than CMessageRefinements.i.dfy,
  // since they depend on PaxosDemarshallData
  ////////////////////////////////////////////////////////////////////////
  function AbstractifyBufferToRslPacket(src:EndPoint, dst:EndPoint, data:seq<byte>) : RslPacket
    requires EndPointIsValidIPV4(src)
    requires EndPointIsValidIPV4(dst)
  {
    LPacket(AbstractifyEndPointToNodeIdentity(dst),
            AbstractifyEndPointToNodeIdentity(src),
            AbstractifyCMessageToRslMessage(PaxosDemarshallData(data)))
  }

  predicate BufferRefinementAgreesWithMessageRefinement(msg:CMessage, marshalled:seq<byte>)
    requires CMessageIsAbstractable(msg)
    requires CMessageIsAbstractable(msg)
  {
    forall src, dst :: (EndPointIsValidIPV4(src) && EndPointIsValidIPV4(dst)) ==>

                         (AbstractifyBufferToRslPacket(src, dst, marshalled)
                          == LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCMessageToRslMessage(msg)))
  }

  function AbstractifyNetPacketToRslPacket(net:UdpPacket) : RslPacket
    requires NetPacketIsAbstractable(net)
  {
    AbstractifyBufferToRslPacket(net.src, net.dst, net.msg)
  }

  predicate NetPacketIsAbstractable(net:UdpPacket)
  {
    && EndPointIsValidIPV4(net.src)
    && EndPointIsValidIPV4(net.dst)
  }

  predicate NetPacketsIsAbstractable(netps:set<UdpPacket>)
  {
    forall p :: p in netps ==> NetPacketIsAbstractable(p)
  }

  lemma lemma_CMessageGrammarValid()
    ensures ValidGrammar(CMessage_grammar())
  {
    var g := CMessage_grammar();
    assert |g.cases| < 0x1_0000_0000_0000_0000;
    assert ValidGrammar(CMessage_Request_grammar());
    assert ValidGrammar(CMessage_1a_grammar());
    assert ValidGrammar(CMessage_1b_grammar());
    assert ValidGrammar(CMessage_1c_grammar());
    assert ValidGrammar(CMessage_2av_grammar());
    assert ValidGrammar(CMessage_2b_grammar());
    assert ValidGrammar(CMessage_Heartbeat_grammar());
    assert ValidGrammar(CMessage_Reply_grammar());
    // assert ValidGrammar(CMessage_AppStateRequest_grammar());
    // assert ValidGrammar(CMessage_AppStateSupply_grammar());
    assert ValidGrammar(CMessage_StartingPhase2_grammar());
  }

  method PaxosMarshall(msg:CMessage) returns (data:array<byte>)
    requires CMessageIsAbstractable(msg)
    requires Marshallable(msg)
    ensures fresh(data)
    ensures NetPacketBound(data[..])
    ensures Marshallable(PaxosDemarshallData(data[..]))
    ensures BufferRefinementAgreesWithMessageRefinement(msg, data[..])
  {
    // var marshall_start_time := Time.GetDebugTimeTicks();
    var val := MarshallMessage(msg);
    lemma_PaxosMarshall(msg, val);
    // var marshall_end_time := Time.GetDebugTimeTicks();
    // RecordTimingSeq("PaxosMarshall_MarshallMessage", marshall_start_time, marshall_end_time);
    lemma_MarshallableBound(msg, val);
    lemma_CMessageGrammarValid();
    // var generic_marshall_start_time := Time.GetDebugTimeTicks();
    data := Marshall(val, CMessage_grammar());
    // var generic_marshall_end_time := Time.GetDebugTimeTicks();

    assert !msg.CMessage_Invalid?;
    if msg.CMessage_Request? {
      // RecordTimingSeq("GenericMarshallMessage_Request", generic_marshall_start_time, generic_marshall_end_time);
    } else if msg.CMessage_1a? {
      // RecordTimingSeq("GenericMarshallMessage_1a", generic_marshall_start_time, generic_marshall_end_time);
    } else if msg.CMessage_1b? {
      // RecordTimingSeq("GenericMarshallMessage_1b", generic_marshall_start_time, generic_marshall_end_time);
    } else if msg.CMessage_1c? {
      // RecordTimingSeq("GenericMarshallMessage_1c", generic_marshall_start_time, generic_marshall_end_time);
    } else if msg.CMessage_2av? {
      // RecordTimingSeq("GenericMarshallMessage_2av", generic_marshall_start_time, generic_marshall_end_time);
    } else if msg.CMessage_2b? {
      // RecordTimingSeq("GenericMarshallMessage_2b", generic_marshall_start_time, generic_marshall_end_time);
    } else if msg.CMessage_Heartbeat? {
      // RecordTimingSeq("GenericMarshallMessage_Heartbeat", generic_marshall_start_time, generic_marshall_end_time);
    } else if msg.CMessage_Reply? {
      // RecordTimingSeq("GenericMarshallMessage_Reply", generic_marshall_start_time, generic_marshall_end_time);
    } 
    // else if msg.CMessage_AppStateRequest? {
    //   // RecordTimingSeq("GenericMarshallMessage_AppStateRequest", generic_marshall_start_time, generic_marshall_end_time);
    // } else if msg.CMessage_AppStateSupply? {
    //   // RecordTimingSeq("GenericMarshallMessage_AppStateSupply", generic_marshall_start_time, generic_marshall_end_time);
    // } 
    else if msg.CMessage_StartingPhase2? {
      // RecordTimingSeq("GenericMarshallMessage_StartingPhase2", generic_marshall_start_time, generic_marshall_end_time);
    }

    forall src, dst | EndPointIsValidIPV4(src) && EndPointIsValidIPV4(dst)
      ensures AbstractifyBufferToRslPacket(src, dst, data[..])
           == LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCMessageToRslMessage(msg));
    {
      calc {
        AbstractifyBufferToRslPacket(src, dst, data[..]);
        LPacket(AbstractifyEndPointToNodeIdentity(dst),
                AbstractifyEndPointToNodeIdentity(src),
                AbstractifyCMessageToRslMessage(PaxosDemarshallData(data[..])));
        LPacket(AbstractifyEndPointToNodeIdentity(dst),
                AbstractifyEndPointToNodeIdentity(src),
                AbstractifyCMessageToRslMessage(PaxosDemarshallData(data[..])));
        LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCMessageToRslMessage(msg));
      }
    }
    lemma_PaxosMarshall2(msg, data);
  }

  lemma {:axiom} lemma_PaxosMarshall(c:CMessage, val:V)
    ensures Marshallable(c)
    ensures ValInGrammar(val, CMessage_grammar())
    ensures ValidVal(val)
    ensures parse_Message(val) == c
    ensures 0 <= SizeOfV(val) < 0x1_0000_0000_0000_0000

  lemma {:axiom} lemma_PaxosMarshall2(c:CMessage, data:array<byte>)
    requires CMessageIsAbstractable(c)
    requires Marshallable(c)
    ensures NetPacketBound(data[..])
    ensures Marshallable(PaxosDemarshallData(data[..]))
    ensures BufferRefinementAgreesWithMessageRefinement(c, data[..])

  //////////////////////////////////////////////////////////////////////////////
  // Sendable predicates

  predicate CPacketIsSendable(cpacket:CPacket)
  {
    && CMessageIsMarshallable(cpacket.msg)
    && CPacketIsAbstractable(cpacket)
    && EndPointIsValidIPV4(cpacket.src)
  }

  // function method EndPointIsValidPublicKey(endPoint:EndPoint) : bool
  // {
  //   && |endPoint.public_key| < 0x10_0000 // < 1 MB
  // }

  // predicate CBroadcastIsAbstractable(broadcast:CBroadcast)
  // {
  //   || broadcast.CBroadcastNop?
  //   || (&& broadcast.CBroadcast?
  //      && EndPointIsValidPublicKey(broadcast.src)
  //      && (forall i :: 0 <= i < |broadcast.dsts| ==> EndPointIsValidPublicKey(broadcast.dsts[i]))
  //      && CMessageIsAbstractable(broadcast.msg))
  // }

  // // predicate method CAppRequestMarshallable(request:CAppRequest)
  // // {
  // //   |request| <= MaxAppRequestSize()
  // // }

  predicate CBroadcastIsValid(broadcast:CBroadcast)
  {
    && CBroadcastIsAbstractable(broadcast)
    && (broadcast.CBroadcast? ==>
         && Marshallable(broadcast.msg)
         && 0 <= |broadcast.dsts| < 0xFFFF_FFFF_FFFF_FFFF
            )
  }

  predicate OutboundPacketsIsValid(out:OutboundPackets)
  {
    OutboundPacketsIsAbstractable(out)
    &&
    (
    match out
    case Broadcast(broadcast) => CBroadcastIsValid(broadcast)
    case OutboundPacket(p) => p.Some? ==> CPacketIsSendable(p.v)
    case PacketSequence(s) => (forall p :: p in s ==> CPacketIsSendable(p))
    )
    // case PacketSequence(s) => |s| < 0xFFFF_FFFF_FFFF_FFFF
    //                           && (forall p :: p in s ==> CPacketIsSendable(p))
    //  case OutboundPacket(Some(p)) => CPacketIsSendable(p)
    //  case OutboundPacket(None) => true
  }


  function AbstractifyUdpPacketToRslPacket(udp:UdpPacket) : RslPacket
    requires UdpPacketIsAbstractable(udp)
  {
    AbstractifyBufferToRslPacket(udp.src, udp.dst, udp.msg)
  }

  predicate UdpPacketIsAbstractable(udp:UdpPacket)
  {
    && EndPointIsValidIPV4(udp.src)
    && EndPointIsValidIPV4(udp.dst)
  }

  predicate UdpPacketsIsAbstractable(udpps:set<UdpPacket>)
  {
    forall p :: p in udpps ==> UdpPacketIsAbstractable(p)
  }

  predicate UdpPacketBound(data:seq<byte>)
  {
    |data| < MaxPacketSize()
  }


}
