include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaImpl.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplReadClock.i.dfy"
include "ReplicaImplProcessPacketNoClock.i.dfy"
include "UdpRSL.i.dfy"
include "CClockReading.i.dfy"
include "Unsendable.i.dfy"

module LiveRSL__ReplicaImplProcessPacketX_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__QRelations_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__ReplicaImplClass_i
import opened LiveRSL__ReplicaImplReadClock_i
import opened LiveRSL__ReplicaImplProcessPacketNoClock_i
import opened LiveRSL__ReplicaModel_i
// import opened LiveRSL__CReplica_i
import opened LiveRSL__Types_i
import opened LiveRSL__UdpRSL_i
import opened LiveRSL__Unsendable_i
import opened Common__UdpClient_i
import opened Environment_s
import opened Common__Util_i

method ReplicaNextProcessPacketTimeout(r:ReplicaImpl, ghost old_net_history:seq<UdpEvent>, ghost timeout_event:UdpEvent)
  returns (ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  requires r.Env().udp.history() == old_net_history + [ timeout_event ]
  requires timeout_event.LIoOpTimeoutReceive?
  ensures  Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
  ensures  RawIoConsistentWithSpecIO(UdpEventLog, ios)
  ensures  old_net_history + UdpEventLog == r.Env().udp.history()
  ensures  OnlySentMarshallableData(UdpEventLog)
{
  ios := [ LIoOpTimeoutReceive() ];
  UdpEventLog := [ timeout_event ];
  lemma_EstablishQLReplicaNextProcessPacketFromTimeout(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios);
}

method ReplicaNextProcessPacketUnmarshallable(
  r:ReplicaImpl,
  ghost old_net_history:seq<UdpEvent>,
  rr:ReceiveResult,
  ghost receive_event:UdpEvent
  ) returns (
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires r.Env().udp.history() == old_net_history + [receive_event]
  requires rr.RRPacket?
  requires receive_event.LIoOpReceive?
  requires !Marshallable(rr.cpacket.msg)
  requires NetPacketIsAbstractable(receive_event.r)
  requires CPacketIsAbstractable(rr.cpacket)
  requires AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyNetPacketToRslPacket(receive_event.r)
  // requires PaxosEndPointIsValid(rr.cpacket.src, r.replica.constants.all.config)
  requires rr.cpacket.msg == PaxosDemarshallData(receive_event.r.msg)
  ensures  IosReflectIgnoringUnsendable(UdpEventLog)
  ensures  RawIoConsistentWithSpecIO(UdpEventLog, ios)
  ensures  old_net_history + UdpEventLog == r.Env().udp.history()
  ensures  OnlySentMarshallableData(UdpEventLog)
{
  ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRslPacket(receive_event.r));
  UdpEventLog := [receive_event];
  ios := [receive_io];
}

method ReplicaNextProcessPacketHeartbeat(
  r:ReplicaImpl,
  ghost old_net_history:seq<UdpEvent>,
  rr:ReceiveResult,
  ghost receive_event:UdpEvent
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires r.Env().udp.history() == old_net_history + [receive_event]
  requires rr.RRPacket?
  requires receive_event.LIoOpReceive?
  requires rr.cpacket.msg.CMessage_Heartbeat?
  requires NetPacketIsAbstractable(receive_event.r)
  requires CPacketIsSendable(rr.cpacket)
  requires AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyNetPacketToRslPacket(receive_event.r)
  // requires PaxosEndPointIsValid(rr.cpacket.src, r.replica.constants.all.config)
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures  r.Repr == old(r.Repr)
  ensures  r.netClient != null
  ensures  ok == UdpClientOk(r.netClient)
  ensures  r.Env().Valid() && r.Env().ok.ok() ==> ok
  ensures  r.Env() == old(r.Env());
  ensures  ok ==>
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && OnlySentMarshallableData(UdpEventLog)
            && old_net_history + UdpEventLog == r.Env().udp.history()
{
  ok := true;
  // var process_start_time := Time.GetDebugTimeTicks();
  ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRslPacket(receive_event.r));
  assert r.ReceivedPacketProperties(rr.cpacket, receive_event, receive_io);

  ghost var midEnv := r.Env();
  assert midEnv == old(r.Env());
  ok, UdpEventLog, ios := Replica_Next_ReadClockAndProcessPacket(r, rr.cpacket, old_net_history, receive_event, receive_io);
  assert ok ==> (r.Env()==midEnv==old(r.Env()));
  if (ok) {
    assert Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios);
  }

  // var end_time := Time.GetDebugTimeTicks();
  // RecordTimingSeq("Replica_Next_ProcessPacket_work", process_start_time, end_time);
  reveal Q_LReplica_Next_ProcessPacket();
}
    
method ReplicaNextProcessPacketNonHeartbeat(
  r:ReplicaImpl,
  ghost old_net_history:seq<UdpEvent>,
  rr:ReceiveResult,
  ghost receive_event:UdpEvent
  ) returns (
  ok:bool,
  ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>
  )
  requires r.Valid()
  requires r.Env().udp.history() == old_net_history + [receive_event]
  requires rr.RRPacket?
  requires receive_event.LIoOpReceive?
  requires !rr.cpacket.msg.CMessage_Heartbeat?
  requires NetPacketIsAbstractable(receive_event.r)
  requires CConfigurationIsValid(r.replica.constants.all.config)
  //  requires Replica_Next_Process_AppStateSupply_Preconditions(r.replica,rr.cpacket)
  requires CPacketIsSendable(rr.cpacket)
  requires AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyNetPacketToRslPacket(receive_event.r)
  // requires PaxosEndPointIsValid(rr.cpacket.src, r.replica.constants.all.config)
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures  r.Repr == old(r.Repr)
  ensures  r.netClient != null
  ensures  ok == UdpClientOk(r.netClient)
  ensures  r.Env().Valid() && r.Env().ok.ok() ==> ok
  ensures  r.Env() == old(r.Env());
  ensures  ok ==>
             && r.Valid()
             && r.nextActionIndex == old(r.nextActionIndex)
             && Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
             && RawIoConsistentWithSpecIO(UdpEventLog, ios)
             && OnlySentMarshallableData(UdpEventLog)
             && old_net_history + UdpEventLog == r.Env().udp.history()
{
  ok := true;
  //var process_start_time := Time.GetDebugTimeTicks();
  ghost var receive_io := LIoOpReceive(AbstractifyNetPacketToRslPacket(receive_event.r));
  assert r.ReceivedPacketProperties(rr.cpacket, receive_event, receive_io);
  // print ("Replica_Next_ProcessPacket: Received a Hearbeat message\n");
  ghost var midEnv := r.Env();
  assert midEnv == old(r.Env());
  ok, UdpEventLog, ios := Replica_Next_ProcessPacketWithoutReadingClock_body(r, rr.cpacket, old_net_history, receive_event, receive_io);
  assert ok ==> (r.Env()==midEnv==old(r.Env()));
  if (ok) {
    lemma_EstablishQLReplicaNextProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios);
  }

  //var end_time := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_ProcessPacket_work", process_start_time, end_time);
}

method Replica_Next_ProcessPacketX(r:ReplicaImpl)
  returns (ok:bool, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
  requires CConfigurationIsValid(r.replica.constants.all.config)
  //  requires Replica_Next_Process_AppStateSupply_Preconditions(r.replica,r.cpacket)
  modifies r.Repr, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
  ensures r.Env().Valid() && r.Env().ok.ok() ==> ok
  ensures r.Env() == old(r.Env());
  ensures ok ==> 
            && r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && (|| Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
                || (&& IosReflectIgnoringUnsendable(UdpEventLog)
                   && old(r.AbstractifyToLReplica()) == r.AbstractifyToLReplica()))
            && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            && OnlySentMarshallableData(UdpEventLog)
            && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
{
  ghost var old_net_history := r.Env().udp.history();
  // var start_time := Time.GetDebugTimeTicks();
  var rr;
  ghost var receive_event;
  //print ("Replica_Next_ProcessPacket: Enter\n");
  // print ("Replica_Next_ProcessPacket: Calling Receive for a packet\n");
  rr, receive_event := Receive(r.netClient, r.localAddr, r.replica.constants.all.config, r.msg_grammar);
  //var receive_packet_time := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_Receive", start_time, receive_packet_time);
  assert r.Env()==old(r.Env());

  if (rr.RRFail?) {
    ok := false;
    //var end_time := Time.GetDebugTimeTicks();
    //RecordTimingSeq("Replica_Next_ProcessPacket_fail", start_time, end_time);
    return;
  } else if (rr.RRTimeout?) {
    ok := true;
    UdpEventLog, ios := ReplicaNextProcessPacketTimeout(r, old_net_history, receive_event);
    //var end_time := Time.GetDebugTimeTicks();
    //RecordTimingSeq("Replica_Next_ProcessPacket_timeout", start_time, end_time);
  } else {
    var marshallable := DetermineIfMessageMarshallable(rr.cpacket.msg);
    if !marshallable {
      ok := true;
      UdpEventLog, ios := ReplicaNextProcessPacketUnmarshallable(r, old_net_history, rr, receive_event);
    } else if (rr.cpacket.msg.CMessage_Heartbeat?) {
      ok, UdpEventLog, ios := ReplicaNextProcessPacketHeartbeat(r, old_net_history, rr, receive_event);
    } else {
      ok, UdpEventLog, ios := ReplicaNextProcessPacketNonHeartbeat(r, old_net_history, rr, receive_event);
    }
  }
  //print ("Replica_Next_ProcessPacket: Exit\n");
}

}
