include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/ByzRSL/Replica.i.dfy"
include "../ByzRSL/ReplicaImpl.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplDelivery.i.dfy"
include "UdpRSL.i.dfy"
include "../ByzRSL/CClockReading.i.dfy"

module LiveByzRSL__ReplicaImplNoReceiveNoClock_i {

  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened Collections__Seqs_i
  import opened Math__mod_auto_i
  import opened LiveByzRSL__CClockReading_i
  import opened LiveByzRSL__CMessage_i
  import opened LiveByzRSL__CMessageRefinements_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__Environment_i
  import opened LiveByzRSL__QRelations_i
  import opened LiveByzRSL__Replica_i
  import opened LiveByzRSL__ReplicaImplLemmas_i
  import opened LiveByzRSL__ReplicaImplClass_i
  import opened LiveByzRSL__ReplicaImplDelivery_i
  import opened LiveByzRSL__ReplicaModel_i
  import opened LiveByzRSL__PacketParsing_i
    // import opened LiveRSL__ReplicaModel_Part3_i
    // import opened LiveRSL__ReplicaModel_Part5_i
    // import opened LiveRSL__CReplica_i
  import opened LiveByzRSL__Types_i
  import opened LiveByzRSL__UdpRSL_i
  import opened Common__UdpClient_i
  import opened Environment_s

  lemma lemma_RevealQFromReplicaNextSpontaneousMaybeEnterNewViewAndSend1aPostconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    requires Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica, replica', packets_sent)
    ensures  Q_LReplica_Next_Spontaneous_MaybeEnterNewViewAndSend1a(replica, AbstractifyCReplicaToLReplica(replica'),
                                                                    AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  {
    reveal Q_LReplica_Next_Spontaneous_MaybeEnterNewViewAndSend1a();
  }

  method ReplicaNoReceiveNoClockNextSpontaneousMaybeEnterNewViewAndSend1a(r:ReplicaImpl)
    returns (ok:bool, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
    requires r.nextActionIndex==1
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures r.Env() == old(r.Env());
    ensures ok ==>
              && r.Valid()
              && r.nextActionIndex == old(r.nextActionIndex)
              && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
              && RawIoConsistentWithSpecIO(UdpEventLog, ios)
              && OnlySentMarshallableData(UdpEventLog)
              && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
  {
    ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
    var sent_packets;

    var (t0, t1) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(r.replica);
    r.replica := t0;
    sent_packets := t1;

    lemma_RevealQFromReplicaNextSpontaneousMaybeEnterNewViewAndSend1aPostconditions(replica_old, r.replica, sent_packets);

    ok, UdpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
    if (!ok) { return; }
    assert old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history(); // deleteme

    assert SpontaneousIos(ios, 0);
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
    assert r.Env() == old(r.Env());
    assert RawIoConsistentWithSpecIO(UdpEventLog, ios);
    lemma_EstablishQLReplicaNoReceiveNextFromNoClock(replica_old, r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
  }

  lemma lemma_RevealQFromReplicaNextSpontaneousMaybeEnterPhase2Postconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    requires Replica_Next_MaybeEnterPhase2_Postconditions(replica, replica', packets_sent)
    ensures  Q_LReplica_Next_Spontaneous_MaybeEnterPhase2(replica, AbstractifyCReplicaToLReplica(replica'),
                                                          AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  {
    reveal Q_LReplica_Next_Spontaneous_MaybeEnterPhase2();
  }

  method ReplicaNoReceiveNoClockNextSpontaneousMaybeEnterPhase2(r:ReplicaImpl)
    returns (ok:bool, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
    requires r.nextActionIndex==2
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures r.Env() == old(r.Env());
    ensures ok ==>
              && r.Valid()
              && r.nextActionIndex == old(r.nextActionIndex)
              && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
              && RawIoConsistentWithSpecIO(UdpEventLog, ios)
              && OnlySentMarshallableData(UdpEventLog)
              && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
  {
    ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
    var sent_packets;
    // r.replica,sent_packets := CReplicaNextSpontaneousMaybeEnterPhase2(r.replica);
    var (t0, t1) := CReplicaNextSpontaneousMaybeEnterPhase2(r.replica);
    r.replica := t0;
    sent_packets := t1;

    lemma_RevealQFromReplicaNextSpontaneousMaybeEnterPhase2Postconditions(replica_old, r.replica, sent_packets);

    ok, UdpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
    if (!ok) { return; }
    assert old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history(); // deleteme

    assert SpontaneousIos(ios, 0);
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
    assert r.Env() == old(r.Env());
    assert RawIoConsistentWithSpecIO(UdpEventLog, ios);
    lemma_EstablishQLReplicaNoReceiveNextFromNoClock(replica_old, r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
  }

  
  lemma lemma_RevealQFromReplicaNextSpontaneousMaybeDecide2bValPostconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    requires Replica_Next_Spontaneous_MaybeDecide2bVal_Postconditions(replica, replica', packets_sent)
    ensures  Q_LReplica_Next_Spontaneous_MaybeDecide2bVal(replica, AbstractifyCReplicaToLReplica(replica'),
                                                           AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  {
    reveal Q_LReplica_Next_Spontaneous_MaybeDecide2bVal();
  }

  
  method {:fuel AbstractifyCReplicaToLReplica,0,0} {:fuel CReplicaIsValid,0,0} ReplicaNoReceiveNoClockNextSpontaneousMaybeDecide2bVal(r:ReplicaImpl)
    returns (ok:bool, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
    requires r.nextActionIndex==4
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures r.Env() == old(r.Env());
    ensures ok ==>
              && r.Valid()
              && r.nextActionIndex == old(r.nextActionIndex)
              && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
              && RawIoConsistentWithSpecIO(UdpEventLog, ios)
              && OnlySentMarshallableData(UdpEventLog)
              && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
  {
    ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
    var sent_packets;
    var replica;
    // r.replica,sent_packets := CReplicaNextSpontaneousMaybeMakeDecision(r.replica);
    assert CReplicaIsValid(r.replica);
    replica, sent_packets := CReplicaNextSpontaneousMaybeDecide2bVal(r.replica);
    assert CReplicaIsValid(replica);
    // assert ConstantsStayConstant_Replica(r.replica, replica);
    assert replica.constants == r.replica.constants;
    r.replica := replica;

    lemma_RevealQFromReplicaNextSpontaneousMaybeDecide2bValPostconditions(replica_old, r.replica, sent_packets);

    assert CReplicaIsAbstractable(r.replica);
    assert CReplicaIsValid(r.replica);
    assert r.Valid();
    ok, UdpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
    if (!ok) { return; }
    assert old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history(); // deleteme

    assert SpontaneousIos(ios, 0);
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
    assert r.Env() == old(r.Env());
    assert RawIoConsistentWithSpecIO(UdpEventLog, ios);
    lemma_EstablishQLReplicaNoReceiveNextFromNoClock(replica_old, r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
  }

  lemma lemma_RevealQFromReplicaNextSpontaneousMaybeSend2bPostconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    requires Replica_Next_MaybeSend2b_Postconditions(replica, replica', packets_sent)
    ensures  Q_LReplica_Next_Spontaneous_MaybeSend2b(replica, AbstractifyCReplicaToLReplica(replica'),
                                                                    AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  {
    reveal Q_LReplica_Next_Spontaneous_MaybeSend2b();
  }

  method ReplicaNoReceiveNoClockNextSpontaneousMaybeSend2b(r:ReplicaImpl)
    returns (ok:bool, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
    requires r.nextActionIndex==5
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures r.Env() == old(r.Env());
    ensures ok ==>
              && r.Valid()
              && r.nextActionIndex == old(r.nextActionIndex)
              && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
              && RawIoConsistentWithSpecIO(UdpEventLog, ios)
              && OnlySentMarshallableData(UdpEventLog)
              && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
  {
    ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
    var sent_packets;

    var (t0, t1) := CReplicaNextSpontaneousMaybeSend2b(r.replica);
    r.replica := t0;
    sent_packets := t1;

    lemma_RevealQFromReplicaNextSpontaneousMaybeSend2bPostconditions(replica_old, r.replica, sent_packets);

    ok, UdpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
    if (!ok) { return; }
    assert old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history(); // deleteme

    assert SpontaneousIos(ios, 0);
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
    assert r.Env() == old(r.Env());
    assert RawIoConsistentWithSpecIO(UdpEventLog, ios);
    lemma_EstablishQLReplicaNoReceiveNextFromNoClock(replica_old, r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
  }


  lemma lemma_RevealQFromReplicaNextSpontaneousTruncateLogBasedOnCheckpointsPostconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(replica, replica', packets_sent)
    ensures  Q_LReplica_Next_Spontaneous_TruncateLogBasedOnCheckpoints(replica, AbstractifyCReplicaToLReplica(replica'),
                                                                       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
  {
    reveal Q_LReplica_Next_Spontaneous_TruncateLogBasedOnCheckpoints();
  }

  method ReplicaNoReceiveNoClockNextSpontaneousTruncateLogBasedOnCheckpoints(r:ReplicaImpl)
    returns (ok:bool, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
    requires r.nextActionIndex==6
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures r.Env() == old(r.Env());
    ensures ok ==>
              && r.Valid()
              && r.nextActionIndex == old(r.nextActionIndex)
              && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
              && RawIoConsistentWithSpecIO(UdpEventLog, ios)
              && OnlySentMarshallableData(UdpEventLog)
              && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
  {
    ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
    var sent_packets;
    var replica;
    assert CReplicaIsValid(r.replica);
    replica,sent_packets := CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints_I1(r.replica);
    assert CReplicaIsValid(replica);
    r.replica := replica;
    lemma_RevealQFromReplicaNextSpontaneousTruncateLogBasedOnCheckpointsPostconditions(replica_old, r.replica, sent_packets);

    
    assert CReplicaIsAbstractable(r.replica);
    assert CReplicaIsValid(r.replica);
    
    assert r.Valid();
    assert OutboundPacketsIsValid(sent_packets);
    assert OutboundPacketsIsAbstractable(sent_packets);
    assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);
    ok, UdpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
    if (!ok) { return; }
    assert old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history(); // deleteme

    assert SpontaneousIos(ios, 0);
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
    assert r.Env() == old(r.Env());
    assert RawIoConsistentWithSpecIO(UdpEventLog, ios);
    lemma_EstablishQLReplicaNoReceiveNextFromNoClock(replica_old, r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
  }



  lemma lemma_RevealQFromReplicaNextSpontaneousMaybeMakeDecisionPostconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    requires Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica, replica', packets_sent)
    ensures  Q_LReplica_Next_Spontaneous_MaybeMakeDecision(replica, AbstractifyCReplicaToLReplica(replica'),
                                                           AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  {
    reveal Q_LReplica_Next_Spontaneous_MaybeMakeDecision();
  }

  // lemma {:axiom} lemma_ReplicaValid(r:ReplicaImpl)
  //   ensures r.Valid()

  method {:fuel AbstractifyCReplicaToLReplica,0,0} {:fuel CReplicaIsValid,0,0} ReplicaNoReceiveNoClockNextSpontaneousMaybeMakeDecision(r:ReplicaImpl)
    returns (ok:bool, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
    requires r.nextActionIndex==7
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures r.Env() == old(r.Env());
    ensures ok ==>
              && r.Valid()
              && r.nextActionIndex == old(r.nextActionIndex)
              && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
              && RawIoConsistentWithSpecIO(UdpEventLog, ios)
              && OnlySentMarshallableData(UdpEventLog)
              && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
  {
    ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
    // ghost var oldr := r;
    var sent_packets;
    var replica;
    // r.replica,sent_packets := CReplicaNextSpontaneousMaybeMakeDecision(r.replica);
    assert CReplicaIsValid(r.replica);
    assert r.Valid();
    replica, sent_packets := CReplicaNextSpontaneousMaybeMakeDecision(r.replica);
    assert CReplicaIsValid(replica);
    r.replica := replica;
    // sent_packets := t1;

    lemma_RevealQFromReplicaNextSpontaneousMaybeMakeDecisionPostconditions(replica_old, r.replica, sent_packets);
    // assert oldr.Valid();
    // assert r.netClient == old(r.netClient);
    // assert r.localAddr == old(r.localAddr);
    // assert r.nextActionIndex == old(r.nextActionIndex);
    assert CReplicaIsAbstractable(r.replica);
    assert CReplicaIsValid(r.replica);
    // assume (0 <= r.nextActionIndex as int < 12);
    // assert r.netClient != null;
    // assert UdpClientIsValid(r.netClient);
    // assert r.netClient.LocalEndPoint() == r.localAddr;
    // assert r.netClient.LocalEndPoint() == r.replica.constants.all.config.replica_ids[r.replica.constants.my_index];
    
    // lemma_ReplicaValid(r);
    assert r.Valid();
    assert OutboundPacketsIsValid(sent_packets);
    assert OutboundPacketsIsAbstractable(sent_packets);
    assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);
    ok, UdpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
    if (!ok) { return; }
    assert old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history(); // deleteme

    assert SpontaneousIos(ios, 0);
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
    assert r.Env() == old(r.Env());
    assert RawIoConsistentWithSpecIO(UdpEventLog, ios);
    lemma_EstablishQLReplicaNoReceiveNextFromNoClock(replica_old, r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
  }

  lemma lemma_RevealQFromReplicaNextSpontaneousMaybeExecutePostconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    requires Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica, replica', packets_sent)
    ensures  Q_LReplica_Next_Spontaneous_MaybeExecute(replica, AbstractifyCReplicaToLReplica(replica'),
                                                      AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
  {
    reveal Q_LReplica_Next_Spontaneous_MaybeExecute();
  }

  method ReplicaNoReceiveNoClockNextSpontaneousMaybeExecute(r:ReplicaImpl)
    returns (ok:bool, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
    requires r.nextActionIndex==8
    requires r.Valid()
    modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures r.Env() == old(r.Env());
    ensures ok ==>
              && r.Valid()
              && r.nextActionIndex == old(r.nextActionIndex)
              && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
              && RawIoConsistentWithSpecIO(UdpEventLog, ios)
              && OnlySentMarshallableData(UdpEventLog)
              && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
  {
    ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
    var sent_packets;
    r.replica,sent_packets := CReplicaNextSpontaneousMaybeExecute(r.replica, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable);

    // var (t0, t1) := CReplicaNextSpontaneousMaybeExecute(r.replica);
    // assert CReplicaIsValid(t0);
    // r.replica := t0;
    // sent_packets := t1;
    //, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable);
    lemma_RevealQFromReplicaNextSpontaneousMaybeExecutePostconditions(replica_old, r.replica, sent_packets);
    assert CReplicaIsValid(r.replica);
    ok, UdpEventLog, ios := DeliverOutboundPackets(r, sent_packets);
    if (!ok) { return; }
    assert old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history(); // deleteme

    assert SpontaneousIos(ios, 0);
    assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios);
    assert r.Env() == old(r.Env());
    assert RawIoConsistentWithSpecIO(UdpEventLog, ios);
    assert Q_LReplica_Next_Spontaneous_MaybeExecute(replica_old, r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
    lemma_EstablishQLReplicaNoReceiveNextFromNoClock(replica_old, r.AbstractifyToLReplica(), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), r.nextActionIndex as int, ios);
  }

  method Replica_NoReceive_NoClock_Next(r:ReplicaImpl) returns (ok:bool, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
    requires r.nextActionIndex==1 || r.nextActionIndex==2 || r.nextActionIndex == 4 || r.nextActionIndex == 5 || r.nextActionIndex==6 || r.nextActionIndex==7 || r.nextActionIndex==8
    requires r.Valid()
    modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures r.Env() == old(r.Env());
    ensures ok ==>
              && r.Valid()
              && r.nextActionIndex == old(r.nextActionIndex)
              && Q_LReplica_NoReceive_Next(old(r.AbstractifyToLReplica()), r.nextActionIndex as int, r.AbstractifyToLReplica(), ios)
              && RawIoConsistentWithSpecIO(UdpEventLog, ios)
              && OnlySentMarshallableData(UdpEventLog)
              && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
  {
    if r.nextActionIndex == 1 {
      ok, UdpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeEnterNewViewAndSend1a(r);
    } else if r.nextActionIndex == 2 {
      ok, UdpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeEnterPhase2(r);
    } else if r.nextActionIndex == 4 {
      ok, UdpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeDecide2bVal(r);
    } else if r.nextActionIndex == 5 {
      ok, UdpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeSend2b(r);
    } else if r.nextActionIndex == 6 {
      ok, UdpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousTruncateLogBasedOnCheckpoints(r);
    } else if r.nextActionIndex == 7 {
      ok, UdpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeMakeDecision(r);
    } else if r.nextActionIndex == 8 {
      ok, UdpEventLog, ios := ReplicaNoReceiveNoClockNextSpontaneousMaybeExecute(r);
    }
  }

}
