include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaImpl.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "NetRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplClass_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__AcceptorModel_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CClockReading_i
// import opened LiveRSL__CLastCheckpointedMap_i
import opened LiveRSL__CMessage_i
// import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ElectionModel_i
import opened LiveRSL__Environment_i
import opened LiveRSL__ExecutorModel_i
import opened LiveRSL__LearnerModel_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ParametersState_i
import opened LiveRSL__ProposerModel_i
import opened LiveRSL__Replica_i
// import opened LiveRSL__ConstantsState_i
import opened LiveRSL__ReplicaModel_i
// import opened LiveRSL__ReplicaModel_Part1_i
// import opened LiveRSL__ReplicaState_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__Types_i
import opened LiveRSL__NetRSL_i
import opened Common__GenericMarshalling_i
import opened Common__NetClient_i
import opened Common__Util_i
import opened AppStateMachine_s
import opened LiveRSL__CStateMachine_i
import opened Common__UpperBound_i

class ReplicaImpl
{
  var replica:CReplica;
  var nextActionIndex:uint64;
  var netClient:NetClient?;
  var localAddr:EndPoint;
  // Optimized mutable sets for ElectionState
  // var cur_req_set:MutableSet<CRequestHeader>;
  // var prev_req_set:MutableSet<CRequestHeader>;
  // var reply_cache_mutable:MutableMap<EndPoint, CReply>;
  var msg_grammar:G;

  ghost var Repr : set<object>;

  constructor()
  {
    netClient := null;
    // var empty_MutableMap:MutableMap<EndPoint, CReply> := MutableMap.EmptyMap();
    // reply_cache_mutable := empty_MutableMap;
    // var empty_MutableSet:MutableSet<CRequestHeader> := MutableSet.EmptySet();
    // cur_req_set := empty_MutableSet;
    // prev_req_set := empty_MutableSet;
    var rcs := CReplicaConstants(0, CConstants(CConfiguration([]), CParameters(0, 0, 0, CUpperBoundInfinite(), 0, 0)));
    var election_state := CElectionState(rcs, CBallot(0, 0), {}, 0, 0, [], []);
    var proposer_state :=
      CProposer(rcs, 0, [], CBallot(0, 0), 0, {}, map [], CIncompleteBatchTimerOff(), election_state);
    var acceptor_state :=
      CAcceptor(rcs, CBallot(0, 0), (map []), [], 0);
    var ep := EndPoint([]);
    var learner_state := CLearner(rcs, CBallot(0, 0), map []);
    var app := AppStateMachine.Initialize();
    var app_state := CStateMachine(app);
    var executor_state := CExecutor(rcs, app_state, 0, CBallot(0, 0), COutstandingOpUnknown(), map[]);
    replica := CReplica(rcs, 0, proposer_state, acceptor_state, learner_state, executor_state);
  }

  predicate Valid()
    reads this
    reads this.replica.executor.app.app
    // reads this.cur_req_set
    // reads this.prev_req_set
    // reads this.reply_cache_mutable
    reads if netClient != null then NetClientIsValid.reads(netClient) else {}
  {
    && CReplicaIsAbstractable(replica)
    && CReplicaIsValid(replica)
    && (0 <= nextActionIndex as int < 10)
    && netClient != null
    && NetClientIsValid(netClient)
    && EndPoint(netClient.MyPublicKey()) == localAddr
    && EndPoint(netClient.MyPublicKey()) == replica.constants.all.config.replica_ids[replica.constants.my_index]
    // && ReplicaStateIsValid(replica)
    && Repr == { this } + NetClientRepr(netClient)
    // && cur_req_set != prev_req_set
    // && MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
    // && MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
    // && MutableMap.MapOf(reply_cache_mutable) == replica.executor.reply_cache 
    && msg_grammar == CMessage_grammar()
  }

  function Env() : HostEnvironment
    requires netClient != null
    reads this, NetClientIsValid.reads(netClient)
  {
    netClient.env
  }

  function AbstractifyToLReplica() : LReplica
    reads this
    reads this.replica.executor.app.app
    requires CReplicaIsValid(replica)
  {
    AbstractifyCReplicaToLReplica(replica)
  }

  function AbstractifyToLScheduler() : LScheduler
    reads this
    reads this.replica.executor.app.app
    requires CReplicaIsValid(replica)
  {
    LScheduler(
      AbstractifyCReplicaToLReplica(replica),
      nextActionIndex as int)
  }

  method Replica_Init(
    constants:CReplicaConstants,
    nc:NetClient,
    ghost env_:HostEnvironment
    ) returns (
    ok:bool
    )
    requires CReplicaConstantsIsValid(constants)
    requires env_.Valid() && env_.ok.ok()
    // requires ReplicaConstantsState_IsValid(constants)
    requires WellFormedLConfiguration(AbstractifyCReplicaConstantsToLReplicaConstants(constants).all.config)
    requires NetClientIsValid(nc)
    requires EndPoint(nc.MyPublicKey()) == constants.all.config.replica_ids[constants.my_index]
    requires nc.env == env_
    // requires KnownSendersMatchConfig(constants.all.config)
    modifies this
    ensures ok ==>
            && Valid()
            && Env() == env_
            && this.replica.constants == constants
            && LSchedulerInit(AbstractifyToLScheduler(), AbstractifyCReplicaConstantsToLReplicaConstants(constants))
  {
    netClient := nc;
    // replica, cur_req_set, prev_req_set, reply_cache_mutable := InitReplicaState(constants);
    replica := CReplicaInit(constants);
    nextActionIndex := 0;
    localAddr := replica.constants.all.config.replica_ids[replica.constants.my_index];
    Repr := { this } + NetClientRepr(netClient);
    this.msg_grammar := CMessage_grammar();
    ok := true;
  }

  predicate ReceivedPacketProperties(cpacket:CPacket, netEvent0:NetEvent, io0:RslIo)
    reads this
    requires CConfigurationIsValid(replica.constants.all.config)
  {
    && CPacketIsSendable(cpacket)
    // && PaxosEndPointIsValid(cpacket.src, replica.constants.all.config)
    && io0.LIoOpReceive?
    && NetEventIsAbstractable(netEvent0)
    && io0 == AbstractifyNetEventToRslIo(netEvent0)
    && NetEventIsAbstractable(netEvent0)
    && netEvent0.LIoOpReceive? && AbstractifyCPacketToRslPacket(cpacket) == AbstractifyNetPacketToRslPacket(netEvent0.r)
  }
}


}
