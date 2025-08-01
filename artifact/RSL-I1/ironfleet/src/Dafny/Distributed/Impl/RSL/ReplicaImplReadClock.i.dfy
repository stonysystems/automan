include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaImpl.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplDelivery.i.dfy"
include "UdpRSL.i.dfy"
include "CClockReading.i.dfy"
include "QRelations.i.dfy"

module LiveRSL__ReplicaImplReadClock_i {

import opened LiveRSL__QRelations_i
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
// import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Environment_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaModel_i
// import opened LiveRSL__ReplicaModel_Part4_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__ReplicaImplClass_i
import opened LiveRSL__ReplicaImplDelivery_i
// import opened LiveRSL__CReplica_i
import opened LiveRSL__Types_i
import opened LiveRSL__UdpRSL_i
import opened Environment_s
import opened Common__UdpClient_i
import opened LiveRSL__ConstantsState_i

lemma {:timeLimitMultiplier 2} lemma_ReplicaNextReadClockAndProcessPacketHelper(
  old_history:seq<UdpEvent>,
  pre_clock_history:seq<UdpEvent>,
  pre_delivery_history:seq<UdpEvent>,
  final_history:seq<UdpEvent>,
  receive_event:UdpEvent,
  clock_event:UdpEvent,
  send_events:seq<UdpEvent>,
  all_events:seq<UdpEvent>,
  receive_io:RslIo,
  clock_io:RslIo,
  send_ios:seq<RslIo>,
  ios_head:seq<RslIo>,
  all_ios:seq<RslIo>
  )
  requires pre_clock_history == old_history + [receive_event]
  requires pre_delivery_history == pre_clock_history + [clock_event]
  requires final_history == pre_delivery_history + send_events
  requires all_events == [receive_event, clock_event] + send_events
  requires UdpEventIsAbstractable(receive_event)
  requires receive_io == AbstractifyUdpEventToRslIo(receive_event)
  requires UdpEventIsAbstractable(clock_event)
  requires clock_io == AbstractifyUdpEventToRslIo(clock_event)
  requires RawIoConsistentWithSpecIO(send_events, send_ios)
  requires all_events == [receive_event, clock_event] + send_events
  requires ios_head == [receive_io, clock_io]
  requires all_ios == ios_head + send_ios
  requires receive_io.LIoOpReceive?
  requires clock_io.LIoOpReadClock?
  requires AllIosAreSends(send_ios)
  requires OnlySentMarshallableData(send_events)
  ensures  final_history == old_history + all_events
  ensures  RawIoConsistentWithSpecIO(all_events, all_ios)
  ensures  ExtractSentPacketsFromIos(all_ios) == ExtractSentPacketsFromIos(send_ios)
  ensures  forall io :: io in all_ios[2..] ==> io.LIoOpSend?
  ensures  OnlySentMarshallableData(all_events)
{
  lemma_EstablishAbstractifyRawLogToIos(all_events, all_ios);
  lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head, send_ios);
  assert all_ios[2..] == send_ios;
  forall io | io in send_ios
    ensures io.LIoOpSend?
  {
    var i :| 0 <= i < |send_ios| && io == send_ios[i];  // OBSERVE trigger
  }
  assert AbstractifyRawLogToIos(all_events) == all_ios;

  calc {
    final_history;
    pre_delivery_history + send_events;
    pre_clock_history + [clock_event] + send_events;
    old_history + [receive_event] + [clock_event] + send_events;
    old_history + ([receive_event] + [clock_event]) + send_events;
    old_history + [receive_event, clock_event] + send_events;
      { assert [receive_event] + [clock_event] == [receive_event, clock_event]; }
    old_history + ([receive_event, clock_event] + send_events);
      { assert ([receive_event, clock_event] + send_events) == all_events; }
    old_history + all_events;
  }

  forall io | io in all_events && io.LIoOpSend?
    ensures NetPacketBound(io.s.msg)
    ensures Marshallable(PaxosDemarshallData(io.s.msg))
  {
    assert io in send_events;
  }
}

method {:fuel CReplicaIsValid,0,0} {:timeLimitMultiplier 3} Replica_Next_ReadClockAndProcessPacket(
  r:ReplicaImpl,
  cpacket:CPacket,
  ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo
  ) returns (
  ok:bool,
  ghost net_event_log:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io)
  requires r.Env().udp.history() == old_net_history + [receive_event]
  requires cpacket.msg.CMessage_Heartbeat?
  requires Replica_Next_Process_Heartbeat_Preconditions(r.replica, cpacket)
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr==old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env() == old(r.Env());
  ensures ok ==>
            && r.Valid()
            && CReplicaIsValid(r.replica)
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ReadClockAndProcessPacket_preconditions(ios)
            && ios[0] == receive_io
            && Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(net_event_log, ios)
            && OnlySentMarshallableData(net_event_log)
            && old_net_history + net_event_log == r.Env().udp.history()
{
  var old_r_AbstractifyToLReplica := old(r.AbstractifyToLReplica());
  var clock, clock_event := ReadClock(r.netClient);
  ghost var clock_io := LIoOpReadClock(clock.t as int);
  assert clock.t as int == clock_event.t; // OBSERVE uint64
  assert clock_io == AbstractifyUdpEventToRslIo(clock_event);

  var sent_packets;

  r.replica, sent_packets := CReplicaNextProcessHeartbeat(r.replica, cpacket, clock.t, r.cur_req_set, r.prev_req_set);

  ghost var send_events, send_ios;
  ghost var pre_delivery_history := r.Env().udp.history();
  ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
  if (!ok) { return; }
  ghost var ios_head := [receive_io, clock_io];
  ios := ios_head + send_ios;
  net_event_log := [receive_event, clock_event] + send_events;

  lemma_ReplicaNextReadClockAndProcessPacketHelper(old_net_history, old(r.Env().udp.history()), pre_delivery_history,
                                                   r.Env().udp.history(), receive_event, clock_event, send_events, net_event_log,
                                                   receive_io, clock_io, send_ios, ios_head, ios);

  assert LReplica_Next_ReadClockAndProcessPacket_preconditions(ios);

  assert LReplicaNextReadClockAndProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios);
  assert LReplicaNextProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios);
  assert Q_LReplica_Next_ProcessPacket(old_r_AbstractifyToLReplica, r.AbstractifyToLReplica(), ios) by {
    reveal Q_LReplica_Next_ProcessPacket();
  }
}

}
