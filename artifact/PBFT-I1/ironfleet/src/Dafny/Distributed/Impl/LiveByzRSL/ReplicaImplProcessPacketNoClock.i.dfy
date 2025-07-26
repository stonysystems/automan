include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/ByzRSL/Replica.i.dfy"
include "../ByzRSL/ReplicaImpl.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplDelivery.i.dfy"
include "UdpRSL.i.dfy"
include "../ByzRSL/CClockReading.i.dfy"

module LiveByzRSL__ReplicaImplProcessPacketNoClock_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveByzRSL__AppInterface_i
import opened LiveByzRSL__CClockReading_i
import opened LiveByzRSL__CMessage_i
import opened LiveByzRSL__CMessageRefinements_i
import opened LiveByzRSL__CConfiguration_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__PacketParsing_i
import opened LiveByzRSL__QRelations_i
import opened LiveByzRSL__Replica_i
import opened LiveByzRSL__ConstantsState_i
import opened LiveByzRSL__ReplicaImplLemmas_i
import opened LiveByzRSL__ReplicaImplClass_i
import opened LiveByzRSL__ReplicaImplDelivery_i
import opened LiveByzRSL__ReplicaModel_i
import opened LiveByzRSL__Types_i
import opened LiveByzRSL__UdpRSL_i
import opened Common__UdpClient_i
import opened Environment_s
import opened Logic__Option_i
import opened Common__Util_i

lemma lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(
  cpacket:CPacket,
  sent_packets:OutboundPackets,
  old_net_history:seq<UdpEvent>,
  post_receive_net_history:seq<UdpEvent>,
  current_net_history:seq<UdpEvent>,
  receive_event:UdpEvent,
  send_events:seq<UdpEvent>,
  receive_io:RslIo,
  send_ios:seq<RslIo>
  ) returns (
  UdpEventLog:seq<UdpEvent>,
  ios:seq<RslIo>
  )
  requires post_receive_net_history == old_net_history + [receive_event]
  requires current_net_history == post_receive_net_history + send_events

  // From Receive:
  requires receive_event.LIoOpReceive?
  requires !cpacket.msg.CMessage_Heartbeat?
  requires CPacketIsAbstractable(cpacket)
  requires UdpEventIsAbstractable(receive_event)
  requires AbstractifyCPacketToRslPacket(cpacket) == AbstractifyNetPacketToRslPacket(receive_event.r)
  requires receive_io == AbstractifyUdpEventToRslIo(receive_event)
    
  // From DeliverOutboundPackets:
  requires AllIosAreSends(send_ios)
  requires OutboundPacketsIsAbstractable(sent_packets)
  requires AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(send_ios)
  requires RawIoConsistentWithSpecIO(send_events, send_ios)
  requires OnlySentMarshallableData(send_events)
        
  ensures  RawIoConsistentWithSpecIO(UdpEventLog, ios)
  ensures  |ios| >= 1
  ensures  ios[0] == receive_io
  ensures  AllIosAreSends(ios[1..])
  ensures  current_net_history == old_net_history + UdpEventLog
  ensures  AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == ExtractSentPacketsFromIos(ios)
  ensures  OnlySentMarshallableData(UdpEventLog)
{
  var ios_head := [receive_io];
  ios := ios_head + send_ios;
  UdpEventLog := [receive_event] + send_events;
        
  calc {
    AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets);
    ExtractSentPacketsFromIos(send_ios);
      { lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head, send_ios); }
    ExtractSentPacketsFromIos(ios_head + send_ios);
    ExtractSentPacketsFromIos(ios);
  }

  forall io | io in ios[1..] ensures io.LIoOpSend?
  {
    var idx :| 0<=idx<|ios[1..]| && io==ios[1..][idx];  // because spec uses 'in seq' instead of indexing
    assert io == send_ios[idx];
    assert AllIosAreSends(send_ios);
    assert io.LIoOpSend?;
  }

  assert UdpEventLogIsAbstractable(UdpEventLog);
  assert AbstractifyRawLogToIos(UdpEventLog) == ios;
    
  lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head, send_ios);
}

method {:fuel CReplicaIsValid,0,0} ReplicaNextProcessPacketInvalid(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
   requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_Invalid?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  ensures  LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
  ensures  Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
  ensures  RawIoConsistentWithSpecIO(UdpEventLog, ios)
  ensures  old_net_history + UdpEventLog == r.Env().udp.history()
  ensures  OnlySentMarshallableData(UdpEventLog)
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
  ghost var rreplica := AbstractifyCReplicaToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_Invalid\n");

  var sent_packets := OutboundPacket(None());
  assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == [];

  assert Q_LReplica_Next_Process_Invalid(rreplica, r.AbstractifyToLReplica(), lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));

  ghost var send_events := [];
  ghost var send_ios := [];

  UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(rreplica, AbstractifyCReplicaToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessRequestPostconditions(
  replica:LReplica,
  replica':CReplica,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_Request_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_Request(replica, AbstractifyCReplicaToLReplica(replica'),
                                           AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_Request();
}
    
method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacketRequest(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history() // records all new messages have received
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io) // prove the abstraction relationship between three type
  requires cpacket.msg.CMessage_Request?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io]) // receive_io size > 1 and the first io is receive
  requires Replica_Next_Process_Request_Preconditions(r.replica, cpacket) // packet and CReplica are valid
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr==old(r.Repr) // do not create new instance
  ensures r.netClient != null 
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && OnlySentMarshallableData(UdpEventLog)
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && r.Env() == old(r.Env())
            && old_net_history + UdpEventLog == r.Env().udp.history()
{
  ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  // print("ProcessPacketRequest: Receive Request Packet\n");

  var sent_packets;
  r.replica, sent_packets := CReplicaNextProcessRequest(r.replica, cpacket, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable);
  // var (ta, tb) := CReplicaNextProcessRequest(r.replica, cpacket);
  // r.replica := ta;
  // sent_packets := tb;

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert UdpClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.LocalEndPoint();

  // refinement
  // prove process request action in impl refines the process request action in spec
  lemma_RevealQFromReplicaNextProcessRequestPostconditions(replica_old, r.replica, cpacket, sent_packets);

  // ensure the src of send packet is correct
  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
}

lemma lemma_RevealQFromReplicaNextProcess1aPostconditions(
  replica:LReplica,
  replica':CReplica,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_1a_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_1a(replica, AbstractifyCReplicaToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_1a();
}

method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket1a(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_1a?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_1a_Preconditions(r.replica, cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && OnlySentMarshallableData(UdpEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + UdpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_1a\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  // print("ReplicaNextProcessPacket1a: Receive 1a Packet\n");

  var sent_packets;
  var (t0, t1) := CReplicaNextProcess1a(r.replica, cpacket);
  r.replica := t0;
  sent_packets := t1;

  // r.replica, sent_packets := CReplicaNextProcess1a(r.replica, cpacket);


  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert UdpClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcess1aPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess1bPostconditions(
  replica:LReplica,
  replica':CReplica,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_1b_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_1b(replica, AbstractifyCReplicaToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_1b();
}

method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket1b(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_1b?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_1b_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && OnlySentMarshallableData(UdpEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + UdpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_1b\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  // print("ReplicaNextProcessPacket1b: Receive 1b Packet\n");

  var sent_packets;
  var (t0, t1)  := CReplicaNextProcess1b(r.replica, cpacket);
  r.replica := t0;
  sent_packets := t1;
  // r.replica, sent_packets := CReplicaNextProcess1b(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert UdpClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcess1bPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcessStartingPhase2Postconditions(
  replica:LReplica,
  replica':CReplica,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_StartingPhase2_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_StartingPhase2(replica, AbstractifyCReplicaToLReplica(replica'),
                                                  AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
{
  reveal Q_LReplica_Next_Process_StartingPhase2();
}

method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 5} ReplicaNextProcessPacketStartingPhase2(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_StartingPhase2?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && OnlySentMarshallableData(UdpEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + UdpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_StartingPhase2\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  // print("ReplicaNextProcessPacketStartingPhase2: Receive start phase 2 Packet\n");

  var sent_packets;
  var (t0, t1) := CReplicaNextProcessStartingPhase2(r.replica, cpacket);
  r.replica := t0;
  sent_packets := t1;
  // r.replica, sent_packets := CReplicaNextProcessStartingPhase2(r.replica, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert UdpClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcessStartingPhase2Postconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess1cPostconditions(
  replica:LReplica,
  replica':CReplica,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_1c_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_1c(replica, AbstractifyCReplicaToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_1c();
}

method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 1} ReplicaNextProcessPacket1c(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_1c?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_1c_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && OnlySentMarshallableData(UdpEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + UdpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_2a\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  // print("ReplicaNextProcessPacket1c: Receive 1c Packet\n");

  var sent_packets;
  // r.replica, sent_packets := CReplicaNextProcess2a(r.replica, cpacket);

  var t0, t1 := CReplicaNextProcess1c(r.replica, cpacket);
  r.replica := t0;
  sent_packets := t1;

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert UdpClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcess1cPostconditions(replica_old, r.replica, cpacket, sent_packets);
  assert CReplicaIsAbstractable(r.replica);
  assert CReplicaIsValid(r.replica);
  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}


lemma lemma_RevealQFromReplicaNextProcess2avPostconditions(
  replica:LReplica,
  replica':CReplica,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_2av_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_2av(replica, AbstractifyCReplicaToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_2av();
}

method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket2av(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_2av?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_2av_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && OnlySentMarshallableData(UdpEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + UdpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_2a\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  // print("ReplicaNextProcessPacket2av: Receive 2av Packet\n");

  var sent_packets;
  // r.replica, sent_packets := CReplicaNextProcess2a(r.replica, cpacket);

  var (t0, t1) := CReplicaNextProcess2av(r.replica, cpacket);
  r.replica := t0;
  sent_packets := t1;

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert UdpClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcess2avPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

lemma lemma_RevealQFromReplicaNextProcess2bPostconditions(
  replica:LReplica,
  replica':CReplica,
  inp:CPacket,
  packets_sent:OutboundPackets
  )
  requires Replica_Next_Process_2b_Postconditions(replica, replica', inp, packets_sent)
  ensures  Q_LReplica_Next_Process_2b(replica, AbstractifyCReplicaToLReplica(replica'),
                                      AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent));
{
  reveal Q_LReplica_Next_Process_2b();
}

method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacket2b(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_2b?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  requires Replica_Next_Process_2b_Preconditions(r.replica,cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && OnlySentMarshallableData(UdpEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + UdpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_2b\n");

  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  var sent_packets;
  // r.replica, sent_packets := CReplicaNextProcess2b(r.replica, cpacket);

  // print("ReplicaNextProcessPacket2b: Receive 2b Packet\n");

  var (t0, t1) := CReplicaNextProcess2b(r.replica, cpacket);
  r.replica := t0;
  sent_packets := t1;

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
  assert UdpClientIsValid(r.netClient);
  assert net_addr_old == r.netClient.LocalEndPoint();

  lemma_RevealQFromReplicaNextProcess2bPostconditions(replica_old, r.replica, cpacket, sent_packets);

  assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

  ghost var send_events, send_ios;
  assert r.Valid();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }

  UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

method {:fuel CReplicaIsValid,0,0} ReplicaNextProcessPacketReply(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires cpacket.msg.CMessage_Reply?
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  ensures  LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
  ensures  Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
  ensures  RawIoConsistentWithSpecIO(UdpEventLog, ios)
  ensures  OnlySentMarshallableData(UdpEventLog)
  ensures  old_net_history + UdpEventLog == r.Env().udp.history()
{
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
  ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
  ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_Reply\n");

  // print("ReplicaNextProcessReply: Receive reply Packet\n");

  var sent_packets := Broadcast(CBroadcastNop);
  lemma_YesWeHaveNoPackets();
  reveal Q_LReplica_Next_Process_Reply();
  assert Q_LReplica_Next_Process_Reply(replica_old, r.AbstractifyToLReplica(), lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));

  ghost var send_events := [];
  ghost var send_ios := [];

  calc {
    ExtractSentPacketsFromIos(send_ios);
      { reveal ExtractSentPacketsFromIos(); }
    [];
  }

  UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
                                                                              old_net_history, old(r.Env().udp.history()),
                                                                              r.Env().udp.history(),
                                                                              receive_event, send_events, receive_io, send_ios);
  lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
                                                               lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

// lemma lemma_RevealQFromReplicaNextProcessAppStateRequestPostconditions(
//   replica:LReplica,
//   replica':CReplica,
//   inp:CPacket,
//   packets_sent:OutboundPackets
//   )
//   requires Replica_Next_Process_AppStateRequest_Postconditions(replica, replica', inp, packets_sent)
//   ensures  Q_LReplica_Next_Process_AppStateRequest(replica, AbstractifyCReplicaToLReplica(replica'),
//                                                    AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// {
//   reveal Q_LReplica_Next_Process_AppStateRequest();
// }
    
// method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 2} ReplicaNextProcessPacketAppStateRequest(
//   r:ReplicaImpl,
//   cpacket:CPacket,
//   ghost old_net_history:seq<UdpEvent>,
//   ghost receive_event:UdpEvent,
//   ghost receive_io:RslIo
//   ) returns (
//   ok:bool,
//   ghost UdpEventLog:seq<UdpEvent>,
//   ghost ios:seq<RslIo>
//   )
//   requires r.Valid()
//   requires old_net_history + [receive_event] == r.Env().udp.history()
//   requires CConfigurationIsValid(r.replica.constants.all.config)
//   requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
//   requires cpacket.msg.CMessage_AppStateRequest?
//   requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
//   modifies r.Repr //, r.reply_cache_mutable
//   ensures r.Repr==old(r.Repr)
//   ensures r.netClient != null
//   ensures ok == UdpClientOk(r.netClient)
//   ensures r.Env() == old(r.Env());
//   ensures ok ==>
//             && r.Valid()
//             && r.nextActionIndex == old(r.nextActionIndex)
//             && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
//             && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
//             && RawIoConsistentWithSpecIO(UdpEventLog, ios)
//             && OnlySentMarshallableData(UdpEventLog)
//             && r.Env() == old(r.Env())
//             && old_net_history + UdpEventLog == r.Env().udp.history()
// {
//   //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
//   ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
//   ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
//   //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_AppStateRequest\n");

//   // Mention unchanged predicates over mutable state in the old heap.
//   ghost var net_client_old := r.netClient;
//   ghost var net_addr_old := r.netClient.LocalEndPoint();
//   assert UdpClientIsValid(net_client_old);

//   var sent_packets;
//   // r.replica, sent_packets := CReplicaNextProcessAppStateRequest(r.replica, cpacket);

//   var (t0, t1) := CReplicaNextProcessAppStateRequest(r.replica, cpacket);
//   r.replica := t0;
//   sent_packets := t1;

//   // Mention unchanged predicates over mutable state in the new heap.
//   assert net_client_old == r.netClient;
//   assert UdpClientIsValid(r.netClient);
//   assert net_addr_old == r.netClient.LocalEndPoint();

//   lemma_RevealQFromReplicaNextProcessAppStateRequestPostconditions(replica_old, r.replica, cpacket, sent_packets);

//   assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

//   ghost var send_events, send_ios;
//   assert r.Valid();
//   ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
//   if (!ok) { return; }

//   UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
//                                                                               old_net_history, old(r.Env().udp.history()),
//                                                                               r.Env().udp.history(),
//                                                                               receive_event, send_events, receive_io, send_ios);
//   lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
//                                                                lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
//   //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
// }

// lemma lemma_RevealQFromReplicaNextProcessAppStateSupplyPostconditions(
//   replica:LReplica,
//   replica':CReplica,
//   inp:CPacket,
//   packets_sent:OutboundPackets
//   )
//   requires Replica_Next_Process_AppStateSupply_Postconditions(replica, replica', inp, packets_sent)
//   ensures  Q_LReplica_Next_Process_AppStateSupply(replica, AbstractifyCReplicaToLReplica(replica'),
//                                                   AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// {
//   reveal Q_LReplica_Next_Process_AppStateSupply();
// }

// method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 5} ReplicaNextProcessPacketAppStateSupply(
//   r:ReplicaImpl,
//   cpacket:CPacket,
//   ghost old_net_history:seq<UdpEvent>,
//   ghost receive_event:UdpEvent,
//   ghost receive_io:RslIo
//   ) returns (
//   ok:bool,
//   ghost UdpEventLog:seq<UdpEvent>,
//   ghost ios:seq<RslIo>
//   )
//   requires r.Valid()
//   requires old_net_history + [receive_event] == r.Env().udp.history()
//   requires CConfigurationIsValid(r.replica.constants.all.config)
//   requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
//   requires cpacket.msg.CMessage_AppStateSupply?
//   requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
//   requires Replica_Next_Process_AppStateSupply_Preconditions(r.replica,cpacket)
//   modifies r.Repr
//   ensures r.Repr==old(r.Repr)
//   ensures r.netClient != null
//   ensures ok == UdpClientOk(r.netClient)
//   ensures r.Env() == old(r.Env());
//   ensures ok ==>
//             && r.Valid()
//             && r.nextActionIndex == old(r.nextActionIndex)
//             && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
//             && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
//             && RawIoConsistentWithSpecIO(UdpEventLog, ios)
//             && OnlySentMarshallableData(UdpEventLog)
//             && r.Env() == old(r.Env())
//             && old_net_history + UdpEventLog == r.Env().udp.history()
// {
//   //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Enter\n"); 
//   ghost var replica_old := AbstractifyCReplicaToLReplica(r.replica);
//   ghost var lpacket := AbstractifyCPacketToRslPacket(cpacket);
//   //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Processing a CMessage_AppStateSupply\n");

//   // Mention unchanged predicates over mutable state in the old heap.
//   ghost var net_client_old := r.netClient;
//   ghost var net_addr_old := r.netClient.LocalEndPoint();
//   assert UdpClientIsValid(net_client_old);

//   var sent_packets;
//   // r.replica, sent_packets := CReplicaNextProcessAppStateSupply(r.replica, cpacket);

//   var (t0, t1) := CReplicaNextProcessAppStateSupply(r.replica, cpacket);
//   r.replica := t0;
//   sent_packets := t1;

//   // Mention unchanged predicates over mutable state in the new heap.
//   assert net_client_old == r.netClient;
//   assert UdpClientIsValid(r.netClient);
//   assert net_addr_old == r.netClient.LocalEndPoint();

//   lemma_RevealQFromReplicaNextProcessAppStateSupplyPostconditions(replica_old, r.replica, cpacket, sent_packets);

//   assert OutboundPacketsHasCorrectSrc(sent_packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index]);

//   ghost var send_events, send_ios;
//   assert r.Valid();
//   ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
//   if (!ok) { return; }

//   UdpEventLog, ios := lemma_ReplicaNextProcessPacketWithoutReadingClockHelper(cpacket, sent_packets,
//                                                                               old_net_history, old(r.Env().udp.history()),
//                                                                               r.Env().udp.history(),
//                                                                               receive_event, send_events, receive_io, send_ios);

//   lemma_EstablishQLReplicaNextProcessPacketWithoutReadingClock(replica_old, AbstractifyCReplicaToLReplica(r.replica),
//                                                                lpacket, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets), ios);
//   //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
// }

method {:fuel CReplicaIsValid,0,0} Replica_Next_ProcessPacketWithoutReadingClock_body(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires old_net_history + [receive_event] == r.Env().udp.history()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires NoClockMessage(cpacket.msg)
  requires LReplica_Next_ProcessPacketWithoutReadingClock_preconditions([receive_io])
  // requires cpacket.msg.CMessage_AppStateRequest? ==> Replica_Next_Process_AppStateRequest_Preconditions(r.replica,cpacket)
  // requires cpacket.msg.CMessage_AppStateSupply? ==> Replica_Next_Process_AppStateSupply_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_2b? ==> Replica_Next_Process_2b_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_1c? ==> Replica_Next_Process_1c_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_2av? ==> Replica_Next_Process_2av_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_1a? ==> Replica_Next_Process_1a_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_1b? ==> Replica_Next_Process_1b_Preconditions(r.replica,cpacket)
  requires cpacket.msg.CMessage_Request? ==> Replica_Next_Process_Request_Preconditions(r.replica,cpacket)
  // requires Replica_Next_Process_AppStateSupply_Preconditions(r.replica,cpacket)
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ProcessPacketWithoutReadingClock_preconditions(ios)
            && Q_LReplica_Next_ProcessPacketWithoutReadingClock(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && OnlySentMarshallableData(UdpEventLog)
            && r.Env() == old(r.Env())
            && old_net_history + UdpEventLog == r.Env().udp.history()
{
  if (cpacket.msg.CMessage_Invalid?) {
    ok := true;
    UdpEventLog, ios := ReplicaNextProcessPacketInvalid(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_Request?) {
    ok, UdpEventLog, ios := ReplicaNextProcessPacketRequest(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_1a?) {
    ok, UdpEventLog, ios := ReplicaNextProcessPacket1a(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_1b?) {
    ok, UdpEventLog, ios := ReplicaNextProcessPacket1b(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_StartingPhase2?) {
    ok, UdpEventLog, ios := ReplicaNextProcessPacketStartingPhase2(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_1c?) {
    ok, UdpEventLog, ios := ReplicaNextProcessPacket1c(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_2av?) {
    ok, UdpEventLog, ios := ReplicaNextProcessPacket2av(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_2b?) {
    ok, UdpEventLog, ios := ReplicaNextProcessPacket2b(r, cpacket, old_net_history, receive_event, receive_io);
  } else if (cpacket.msg.CMessage_Reply?) {
    ok := true;
    UdpEventLog, ios := ReplicaNextProcessPacketReply(r, cpacket, old_net_history, receive_event, receive_io);
  } 
  // else if (cpacket.msg.CMessage_AppStateRequest?) {
  //   ok, UdpEventLog, ios := ReplicaNextProcessPacketAppStateRequest(r, cpacket, old_net_history, receive_event, receive_io);
  // } else if (cpacket.msg.CMessage_AppStateSupply?) {
  //   ok, UdpEventLog, ios := ReplicaNextProcessPacketAppStateSupply(r, cpacket, old_net_history, receive_event, receive_io);
  // } 
  else {
    assert false;
  }
  //print ("Replica_Next_ProcessPacketWithoutReadingClock_body: Exit\n");
}

}
