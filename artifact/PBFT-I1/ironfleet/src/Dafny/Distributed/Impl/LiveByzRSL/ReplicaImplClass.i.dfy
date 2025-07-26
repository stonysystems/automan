include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/ByzRSL/Replica.i.dfy"
include "../ByzRSL/ReplicaImpl.i.dfy"
// include "ReplicaImplLemmas.i.dfy"
include "UdpRSL.i.dfy"
include "../ByzRSL/CClockReading.i.dfy"

module LiveByzRSL__ReplicaImplClass_i {

  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened Collections__Seqs_i
  import opened Math__mod_auto_i
  import opened LiveByzRSL__AcceptorModel_i
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__CClockReading_i
    // import opened LiveRSL__CLastCheckpointedMap_i
  import opened LiveByzRSL__CMessage_i
  // import opened LiveRSL__CMessageRefinements_i
  import opened LiveByzRSL__ConstantsState_i
  import opened LiveByzRSL__CConfiguration_i
  import opened LiveByzRSL__Configuration_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__ElectionModel_i
  import opened LiveByzRSL__Environment_i
  import opened LiveByzRSL__ExecutorModel_i
  import opened LiveByzRSL__LearnerModel_i
  import opened LiveByzRSL__PacketParsing_i
  import opened LiveByzRSL__ParametersState_i
  import opened LiveByzRSL__ProposerModel_i
  import opened LiveByzRSL__Replica_i
    // import opened LiveRSL__ConstantsState_i
  import opened LiveByzRSL__ReplicaModel_i
    // import opened LiveRSL__ReplicaModel_Part1_i
    // import opened LiveRSL__CReplica_i
  // import opened LiveByzRSL__ReplicaImplLemmas_i
  import opened LiveByzRSL__Types_i
  import opened LiveByzRSL__UdpRSL_i
  import opened Common__GenericMarshalling_i
  import opened Common__UdpClient_i
  import opened Common__Util_i
  import opened Common__UpperBound_i
    // import opened AppStateMachine_s
    // import opened LiveRSL__CStateMachine_i

  class ReplicaImpl
  {
    var replica:CReplica;
    var nextActionIndex:uint64;
    var netClient:UdpClient?;
    var localAddr:EndPoint;
    // Optimized mutable sets for ElectionState
    var cur_req_set:MutableSet<CRequestHeader>;
    var prev_req_set:MutableSet<CRequestHeader>;
    var reply_cache_mutable:MutableMap<EndPoint, CReply>;
    var msg_grammar:G;

    ghost var Repr : set<object>;

    constructor()
    {
      netClient := null;
      var empty_MutableMap:MutableMap<EndPoint, CReply> := MutableMap.EmptyMap();
      reply_cache_mutable := empty_MutableMap;
      var empty_MutableSet:MutableSet<CRequestHeader> := MutableSet.EmptySet();
      cur_req_set := empty_MutableSet;
      prev_req_set := empty_MutableSet;
      // var rcs := CReplicaConstants(0, CConstants(CConfiguration([]), CParameters(0, 0, 0, CUpperBoundInfinite(), 0, 0)));
      // var election_state := CElectionState(rcs, CBallot(0, 0), {}, 0, 0, [], []);
      // var proposer_state :=
      //   CProposer(rcs, 0, [], CBallot(0, 0), 0, [], map [], CIncompleteBatchTimerOff(), election_state);
      // var acceptor_state :=
      //   CAcceptor(rcs, CBallot(0, 0), (map []), [], 0, [], (map []), 0, CValToBeSent2bUnknown());
      // // var ep := EndPoint([]);
      // var learner_state := CLearner(rcs, CBallot(0, 0), map []);
      // // var app_state := AppStateMachine.Initialize();
      // var app_state := CAppStateInit();
      // var executor_state := CExecutor(rcs, app_state, 0, CBallot(0, 0), COutstandingOpUnknown(), map[]);
      // replica := CReplica(rcs, 0, proposer_state, acceptor_state, learner_state, executor_state);
    }

    predicate Valid()
      reads this
      // reads this.replica.executor.app.app
      reads this.cur_req_set
      reads this.prev_req_set
      reads this.reply_cache_mutable
      reads if netClient != null then UdpClientIsValid.reads(netClient) else {}
    {
      && CReplicaIsAbstractable(replica)
      && CReplicaIsValid(replica)
      && (0 <= nextActionIndex as int < 12)
      && netClient != null
      && UdpClientIsValid(netClient)
      && netClient.LocalEndPoint() == localAddr
      && netClient.LocalEndPoint() == replica.constants.all.config.replica_ids[replica.constants.my_index]
         // && CReplicaIsValid(replica)
      && Repr == { this } + UdpClientRepr(netClient)
      && cur_req_set != prev_req_set
      && MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
      && MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
      && MutableMap.MapOf(reply_cache_mutable) == replica.executor.reply_cache
      && msg_grammar == CMessage_grammar()
    }

    function Env() : HostEnvironment
      requires netClient != null
      reads this, UdpClientIsValid.reads(netClient)
    {
      netClient.env
    }

    function AbstractifyToLReplica() : LReplica
      reads this
      // reads this.replica.executor.app.app
      requires CReplicaIsValid(replica)
    {
      AbstractifyCReplicaToLReplica(replica)
    }

    function AbstractifyToLScheduler() : LScheduler
      reads this
      // reads this.replica.executor.app.app
      requires CReplicaIsValid(replica)
    {
      LScheduler(
        AbstractifyCReplicaToLReplica(replica),
        nextActionIndex as int)
    }


    method ConstructUdpClient(constants:CReplicaConstants, ghost env_:HostEnvironment) returns (ok:bool, client:UdpClient?)
      requires env_.Valid() && env_.ok.ok()
      requires CReplicaConstantsIsValid(constants)
      modifies env_.ok
      ensures ok ==> && client != null
                     && UdpClientIsValid(client)
                     && client.LocalEndPoint() == constants.all.config.replica_ids[constants.my_index]
                     && client.env == env_
    {
      var my_ep := constants.all.config.replica_ids[constants.my_index];
      var ip_byte_array := new byte[|my_ep.addr|];
      assert EndPointIsValidIPV4(my_ep);
      seqIntoArrayOpt(my_ep.addr, ip_byte_array);
      var ip_endpoint;
      ok, ip_endpoint := IPEndPoint.Construct(ip_byte_array, my_ep.port, env_);
      if !ok { return; }
      ok, client := UdpClient.Construct(ip_endpoint, env_);
      if ok {
        calc {
          client.LocalEndPoint();
          ip_endpoint.EP();
          my_ep;
        }
      }
    }


    lemma {:axiom} Replica_Init_Helper1 (constants:CReplicaConstants, env_:HostEnvironment, ok:bool)
      requires env_.Valid() && env_.ok.ok()
      requires CReplicaConstantsIsValid(constants)
      requires WellFormedLConfiguration(AbstractifyCReplicaConstantsToLReplicaConstants(constants).all.config)
      ensures ok ==>
                && Valid()
                && Env() == env_
                && this.replica.constants == constants
                && LSchedulerInit(AbstractifyToLScheduler(), AbstractifyCReplicaConstantsToLReplicaConstants(constants))

    lemma {:axiom} Replica_Init_Helper2 (env_:HostEnvironment)
      ensures env_.Valid() && env_.ok.ok()


    method {:timeLimitMultiplier 7} Replica_Init(constants:CReplicaConstants, ghost env_:HostEnvironment) returns (ok:bool)
      requires env_.Valid() && env_.ok.ok()
      requires CReplicaConstantsIsValid(constants)
      requires WellFormedLConfiguration(AbstractifyCReplicaConstantsToLReplicaConstants(constants).all.config)
      modifies this, netClient
      modifies env_.ok

      ensures ok ==>
                && Valid()
                && Env() == env_
                && this.replica.constants == constants
                && LSchedulerInit(AbstractifyToLScheduler(), AbstractifyCReplicaConstantsToLReplicaConstants(constants))

    {
      ok, netClient := ConstructUdpClient(constants, env_);

      if (ok)
      {
        replica := CReplicaInit(constants);
        nextActionIndex := 0;
        localAddr := replica.constants.all.config.replica_ids[replica.constants.my_index];
        Repr := { this } + UdpClientRepr(netClient);
        this.msg_grammar := CMessage_grammar();
      }

      Replica_Init_Helper2(env_);
      Replica_Init_Helper1(constants, env_, ok);
    }

    predicate ReceivedPacketProperties(cpacket:CPacket, netEvent0:UdpEvent, io0:RslIo)
      reads this
      requires CConfigurationIsValid(replica.constants.all.config)
    {
      && CPacketIsSendable(cpacket)
         // && PaxosEndPointIsValid(cpacket.src, replica.constants.all.config)
      && io0.LIoOpReceive?
      && UdpEventIsAbstractable(netEvent0)
      && io0 == AbstractifyUdpEventToRslIo(netEvent0)
      && UdpEventIsAbstractable(netEvent0)
      && netEvent0.LIoOpReceive? && AbstractifyCPacketToRslPacket(cpacket) == AbstractifyNetPacketToRslPacket(netEvent0.r)
    }
  }


}
