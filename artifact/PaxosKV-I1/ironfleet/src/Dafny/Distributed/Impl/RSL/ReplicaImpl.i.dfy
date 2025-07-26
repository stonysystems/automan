include "../../Protocol/RSL/Replica.i.dfy"
include "CConstants.i.dfy"
include "ProposerImpl.i.dfy"
include "AcceptorImpl.i.dfy"
include "LearnerImpl.i.dfy"
include "ExecutorImpl.i.dfy"
include "CClockReading.i.dfy"
include "../Common/Util.i.dfy"
include "CConstants.i.dfy"
include "../../Common/Collections/Multisets.s.dfy"

module LiveRSL__ReplicaModel_i {
import opened AppStateMachine_s
import opened Native__Io_s
import opened Native__NativeTypes_s
// import opened LiveRSL__AcceptorState_i
import opened LiveRSL__AcceptorModel_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CMessage_i
// import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ElectionModel_i
import opened LiveRSL__ExecutorModel_i
// import opened LiveRSL__LearnerState_i
import opened LiveRSL__LearnerModel_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__Proposer_i
// import opened LiveRSL__ProposerState_i
import opened LiveRSL__ProposerModel_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ConstantsState_i
// import opened LiveRSL__ReplicaState_i
import opened LiveRSL__Types_i
import opened Logic__Option_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CPaxosConfiguration_i
import opened Common__UpperBound_i
import opened Impl__LiveRSL__Broadcast_i
import opened LiveRSL__Configuration_i
import opened Common__Util_i
import opened LiveRSL__Acceptor_i
import opened GenericRefinement_i
import opened Collections__CountMatches_i
import opened Collections__Multisets_s
import opened Collections__Seqs_i

/************************** AutoMan Translation ************************/
  datatype CReplica = 
	CReplica(
		constants: CReplicaConstants, 
		nextHeartbeatTime: int, 
		proposer: CProposer, 
		acceptor: CAcceptor, 
		learner: CLearner, 
		executor: CExecutor
	)

	predicate CReplicaIsValid(s: CReplica) 
	{
		CReplicaIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CProposerIsValid(s.proposer) 
		&& 
		CAcceptorIsValid(s.acceptor) 
		&& 
		CLearnerIsValid(s.learner) 
		&& 
		CExecutorIsValid(s.executor)
    && /** Manually Added */
    s.constants == s.acceptor.constants
	}


	predicate CReplicaIsAbstractable(s: CReplica) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		// CProposerIsAbstractable(s.proposer) 
    CProposerIsValid(s.proposer) 
		&& 
		CAcceptorIsAbstractable(s.acceptor) 
		&& 
		CLearnerIsAbstractable(s.learner) 
		&& 
		CExecutorIsAbstractable(s.executor)
	}

	function AbstractifyCReplicaToLReplica(s: CReplica) : LReplica 
		requires CReplicaIsAbstractable(s)
    // requires CReplicaIsValid(s)
	{
		LReplica(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.nextHeartbeatTime, AbstractifyCProposerToLProposer(s.proposer), AbstractifyCAcceptorToLAcceptor(s.acceptor), AbstractifyCLearnerToLLearner(s.learner), AbstractifyCExecutorToLExecutor(s.executor))
	}

    method CReplicaInit(c: CReplicaConstants) returns (r:CReplica, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>, reply_cache_mutable:MutableMap<EndPoint, CReply>)
		requires CReplicaConstantsIsValid(c)
		// requires CWellFormedLConfiguration(c.all.config)
		// ensures var r := CReplicaInit(c); 
    ensures CReplicaIsValid(r) && LReplicaInit(AbstractifyCReplicaToLReplica(r), AbstractifyCReplicaConstantsToLReplicaConstants(c))
    ensures MutableSet.SetOf(cur_req_set) == r.proposer.election_state.cur_req_set
    ensures MutableSet.SetOf(prev_req_set) == r.proposer.election_state.prev_req_set
    ensures fresh(cur_req_set) && fresh(prev_req_set) && cur_req_set != prev_req_set
    ensures fresh(reply_cache_mutable)
    ensures r.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
	{
    var proposer;
    proposer, cur_req_set, prev_req_set := CProposerInit(c);
    var executor;
    executor, reply_cache_mutable := CExecutorInit(c);
		var t1 := 
			c; 		
		var t2 := 
			0; 		
		// var t3 := 
		// 	CProposerInit(c); 		
		var t4 := 
			CAcceptorInit(c); 		
		var t5 := 
			CLearnerInit(c); 		
		// var t6 := 
		// 	CExecutorInit(c); 		
		r := CReplica(t1, t2, proposer, t4, t5, executor);
	}

  // function method CReplicaInit(c: CReplicaConstants) : CReplica 
	// 	requires CReplicaConstantsIsValid(c)
	// 	// requires CWellFormedLConfiguration(c.all.config)
	// 	ensures var r := CReplicaInit(c); CReplicaIsValid(r) && LReplicaInit(AbstractifyCReplicaToLReplica(r), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	// {
	// 	var t1 := 
	// 		c; 		
	// 	var t2 := 
	// 		0; 		
	// 	var t3 := 
	// 		CProposerInit(c); 		
	// 	var t4 := 
	// 		CAcceptorInit(c); 		
	// 	var t5 := 
	// 		CLearnerInit(c); 		
	// 	var t6 := 
	// 		CExecutorInit(c); 		
	// 	CReplica(t1, t2, t3, t4, t5, t6)
	// }

  function method CReplicaNextProcessInvalid(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Invalid?
		ensures var (s', non_empty_sequential_sent_packets) := CReplicaNextProcessInvalid(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(non_empty_sequential_sent_packets) && LReplicaNextProcessInvalid(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(non_empty_sequential_sent_packets))
	{
		var t1 := 
			s; 		
		var t2 := 
			PacketSequence([]); 		
		(t1, t2)
	}

  method CReplicaNextProcessRequest(
		s : CReplica ,
		received_packet : CPacket,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>, reply_cache_mutable:MutableMap<EndPoint, CReply>
    ) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Request?

    requires s.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    modifies cur_req_set, prev_req_set//, reply_cache_mutable
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set
    ensures  s'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)

		// ensures var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet); 
    ensures CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
    requires Replica_Next_Process_Request_Preconditions(s, received_packet)
    // ensures  
    //   var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet);
    ensures Replica_Next_Process_Request_Postconditions(
        (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)
  {
    lemma_CReplicaNextProcessRequest_pre(s, received_packet);

    // var (s', sequential_sent_packets) := 
    var cached, cached_reply := reply_cache_mutable.TryGetValue(received_packet.src);
    if cached && cached_reply.CReply? && received_packet.msg.seqno_req <= cached_reply.seqno
		// if  && received_packet.src in s.executor.reply_cache && s.executor.reply_cache[received_packet.src].CReply? && received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno
		{ 
			s' :=	s;
			sequential_sent_packets := CExecutorProcessRequest(s.executor, received_packet, reply_cache_mutable);
	
    }
		else
    { 
        var p := CProposerProcessRequest(s.proposer, received_packet, cur_req_set, prev_req_set);
				s' := s.(
					proposer := p
				);
				sequential_sent_packets := OutboundPacket(None());
    }

    lemma_CReplicaNextProcessRequest(s, received_packet, s', sequential_sent_packets);
    // (s', sequential_sent_packets)
	}


  // /** 13 lines of manual code for I1 */
  // method CReplicaNextProcessRequest(s: CReplica, received_packet: CPacket, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_Request?

  //   /** Manually Added for I1 */
  //   requires s.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
  //   requires cur_req_set != prev_req_set
  //   requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
  //   requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
  //   modifies cur_req_set, prev_req_set//, reply_cache_mutable
  //   ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
  //   ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set
  //   ensures  s'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)

  //   ensures CReplicaIsValid(s') 
  //     && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
  //     && OutboundPacketsIsValid(sequential_sent_packets) 
  //     && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	// var t1 := 
  //     var cached, cached_reply := reply_cache_mutable.TryGetValue(received_packet.src); /** Manually Added for I1 */
	// 		if cached && cached_reply.CReply? && received_packet.msg.seqno_req <= cached_reply.seqno { 
	// 			sequential_sent_packets := 
	// 				CExecutorProcessRequest(s.executor, received_packet, reply_cache_mutable); 				
	// 			s' := s; 				
	// 			// (t2, t1) 
  //     } else {
	// 			var t1 := 
	// 				CProposerProcessRequest(s.proposer, received_packet, cur_req_set, prev_req_set); 				
	// 			var sequential_sent_packets := 
	// 				PacketSequence([]); 				
	// 			s' := s.(proposer := t1); 				
	// 			// (t3, t2);
  //     } 		
  //   lemma_Postconditions(s, received_packet, s', sequential_sent_packets); /** Manually Added */
  //   lemma_CReplicaNextProcessRequest(s, received_packet, s', sequential_sent_packets);
	// 	// (t1.0, t1.1)
	// }

  lemma {:axiom} lemma_CReplicaNextProcessRequest(s: CReplica, received_packet: CPacket, s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Request?
    ensures CReplicaIsValid(s') 
      && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sequential_sent_packets) 
      && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))

  function method CReplicaNextProcess1a(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1a?
		ensures 
      var (s', sequential_sent_packets) := CReplicaNextProcess1a(s, received_packet); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sequential_sent_packets) 
      && LReplicaNextProcess1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CAcceptorProcess1a(s.acceptor, received_packet); 		
		var t2 := 
			s.(acceptor := t1.0); 		
    lemma_Postconditions(s, received_packet, t2, t1.1); /** Manually Added */
		(t2, t1.1)
	}

  function method CReplicaNextProcess1b(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1b?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess1b(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcess1b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if received_packet.src in s.proposer.constants.all.config.replica_ids && received_packet.msg.bal_1b == s.proposer.max_ballot_i_sent_1a && s.proposer.current_state == 1 && (forall other_packet :: other_packet in s.proposer.received_1b_packets ==> other_packet.src != received_packet.src) then 
				var t1 := 
					CProposerProcess1b(s.proposer, received_packet); 				
				var t2 := 
					CAcceptorTruncateLog(s.acceptor, received_packet.msg.log_truncation_point); 				
				var t3 := 
					PacketSequence([]); 				
				var t4 := 
					s.(proposer := t1, acceptor := t2); 				
				(t4, t3) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					PacketSequence([]); 				
				(t1, t2); 	
    lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */	
		(t1.0, t1.1)
	}

  function method CReplicaNextProcessStartingPhase2(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_StartingPhase2?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessStartingPhase2(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessStartingPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CExecutorProcessStartingPhase2(s.executor, received_packet); 		
		var t2 := 
			s.(executor := t1.0); 		
    lemma_Postconditions(s, received_packet, t2, t1.1); /** Manually Added */	
		(t2, t1.1)
	}

  function method CReplicaNextProcess2a(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, OutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2a?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess2a(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
    requires Replica_Next_Process_2a_Preconditions(s, received_packet)
    ensures  
      var (s', sequential_sent_packets) := CReplicaNextProcess2a(s, received_packet);
      Replica_Next_Process_2a_Postconditions(
        (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)

  {
		var m := received_packet.msg; 

    var (s', sequential_sent_packets) := 
		if  && received_packet.src in s.acceptor.constants.all.config.replica_ids && CBalLeq(s.acceptor.max_bal, m.bal_2a) && CLeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val)
		then 
			var (t0, t1) := CAcceptorProcess2a(s.acceptor, received_packet); 
			(
				s.(
					acceptor := t0
				),
				t1
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
    ;

    lemma_CReplicaNextProcess2a(s, received_packet, s', sequential_sent_packets);
    (s', sequential_sent_packets)
  }


  // function method CReplicaNextProcess2a(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_2a?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcess2a(s, received_packet); 
  //   CReplicaIsValid(s') 
  //   && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
  //   && OutboundPacketsIsValid(sequential_sent_packets) 
  //   && LReplicaNextProcess2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	var t1 := 
	// 		var m := 
	// 			received_packet.msg; 			
	// 		var t1 := 
	// 			if received_packet.src in s.acceptor.constants.all.config.replica_ids && CBalLeq(s.acceptor.max_bal, m.bal_2a) && CLeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val) then 
	// 				var t1 := 
	// 					CAcceptorProcess2a(s.acceptor, received_packet); 					
	// 				var t2 := 
	// 					s.(acceptor := t1.0); 					
	// 				(t2, t1.1) 
	// 			else 
	// 				var t1 := 
	// 					s; 					
	// 				var t2 := 
	// 					PacketSequence([]); 					
	// 				(t1, t2); 			
	// 		(t1.0, t1.1); 		
  //   lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */	
	// 	(t1.0, t1.1)
	// }

  function method CReplicaNextProcess2b(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, OutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2b?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess2b(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
    requires Replica_Next_Process_2b_Preconditions(s, received_packet)
    ensures
      var (s', sequential_sent_packets) := CReplicaNextProcess2b(s, received_packet); 
      Replica_Next_Process_2b_Postconditions(
        (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)

  {
    lemma_CReplicaNextProcess2b_pre(s, received_packet);

		var opn := received_packet.msg.opn_2b; 
		var op_learnable := s.executor.ops_complete < opn || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.COutstandingOpUnknown?); 
		
    var (s', sequential_sent_packets) := 
    if op_learnable
		then 
			(
				s.(
					learner := CLearnerProcess2b(s.learner, received_packet)
				),
				OutboundPacket(None())
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
    ;

    lemma_CReplicaNextProcess2b(s, received_packet, s', sequential_sent_packets);
    (s', sequential_sent_packets)
	}


  // function method CReplicaNextProcess2b(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_2b?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcess2b(s, received_packet); 
  //   CReplicaIsValid(s') 
  //   && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
  //   && OutboundPacketsIsValid(sequential_sent_packets) 
  //   && LReplicaNextProcess2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	var t1 := 
	// 		var opn := 
	// 			received_packet.msg.opn_2b; 			
	// 		var t1 := 
	// 			var op_learnable := 
	// 				(s.executor.ops_complete < opn) || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.COutstandingOpUnknown?); 				
	// 			var t1 := 
	// 				if op_learnable then 
	// 					var t1 := 
	// 						CLearnerProcess2b(s.learner, received_packet); 						
	// 					var t2 := 
	// 						PacketSequence([]); 						
	// 					var t3 := 
	// 						s.(learner := t1); 						
	// 					(t3, t2) 
	// 				else 
	// 					var t1 := 
	// 						s; 						
	// 					var t2 := 
	// 						PacketSequence([]); 						
	// 					(t1, t2); 				
	// 			(t1.0, t1.1); 			
	// 		(t1.0, t1.1); 	
  //   lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */		
	// 	(t1.0, t1.1)
	// }

  function method CReplicaNextProcessReply(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, OutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Reply?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessReply(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessReply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		(
			s,
			OutboundPacket(None())
		)
	}

  // function method CReplicaNextProcessReply(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_Reply?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcessReply(s, received_packet); 
  //   CReplicaIsValid(s') 
  //   && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
  //   && OutboundPacketsIsValid(sequential_sent_packets) 
  //   && LReplicaNextProcessReply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	var t1 := 
	// 		PacketSequence([]); 		
	// 	var t2 := 
	// 		s; 		
  //   lemma_Postconditions(s, received_packet, t2, t1); /** Manually Added */	
	// 	(t2, t1)
	// }

  /** 13 lines of manual code for I1 */
  method CReplicaNextProcessAppStateSupply(s: CReplica, received_packet: CPacket) returns (s':CReplica, sequential_sent_packets:OutboundPackets, replicaChanged:bool)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateSupply?
		
    /** Manually Added for I1 */
    ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
    ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
    // ensures  replicaChanged ==> fresh(reply_cache_mutable)
    // ensures  replicaChanged ==> s'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
    ensures  !replicaChanged ==> s' == s

    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessAppStateSupply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
    /** Manually Added for I1 */
    var empty_Mutable_Map:MutableMap<EndPoint, CReply> := MutableMap.EmptyMap();
    // reply_cache_mutable := empty_Mutable_Map;

		// var t1 := 
			if received_packet.src in s.executor.constants.all.config.replica_ids && received_packet.msg.opn_state_supply > s.executor.ops_complete { 
				var t1 := 
					CLearnerForgetOperationsBefore(s.learner, received_packet.msg.opn_state_supply); 				
				var e := 
					CExecutorProcessAppStateSupply(s.executor, received_packet); 	

        /** Manually Added for I1 */
        // assert fresh(reply_cache_mutable);
        // assert e.reply_cache == MutableMap.MapOf(reply_cache_mutable);

				sequential_sent_packets := PacketSequence([]); 				
				s' := s.(learner := t1, executor := e); 				
        replicaChanged := true;
				// (t4, t3) 
      } else { 
				s' := s; 				
				sequential_sent_packets := PacketSequence([]); 				
				// (t1, t2); 	
        replicaChanged := false;
      }	
    lemma_CReplicaNextProcessAppStateSupply1(s,received_packet,s',sequential_sent_packets,replicaChanged);
    lemma_Postconditions(s, received_packet, s', sequential_sent_packets); /** Manually Added */
		// (t1.0, t1.1)
	}

  lemma {:axiom} lemma_CReplicaNextProcessAppStateSupply1(s : CReplica ,
		received_packet : CPacket, s':CReplica, sequential_sent_packets:OutboundPackets, replicaChanged:bool)
    // ensures  replicaChanged ==> fresh(reply_cache_mutable)
    // ensures  replicaChanged ==> s'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
    ensures  !replicaChanged ==> s' == s

  method CReplicaNextProcessAppStateRequest(s: CReplica, received_packet: CPacket, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateRequest?
		
    requires s.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
    ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
    ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
    // ensures s'.executor == s.executor

    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessAppStateRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1, t2 := 
			CExecutorProcessAppStateRequest(s.executor, received_packet, reply_cache_mutable); 		
		s' := s.(executor := t1); 	
    sequential_sent_packets := t2;	
    lemma_Postconditions(s, received_packet, s', sequential_sent_packets); /** Manually Added */
		// (t2, t1.1)
	}

  method CReplicaNextProcessHeartbeat(
		s : CReplica ,
		received_packet : CPacket ,
		clock : int,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s' : CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Heartbeat?

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  s'.executor == s.executor
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set

		// ensures var (s', sequential_sent_packets) := CReplicaNextProcessHeartbeat(s, received_packet, clock); 
    ensures CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), clock, AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
    && Replica_Next_Process_Heartbeat_Postconditions(old(AbstractifyCReplicaToLReplica(s)), s',
                                                                received_packet, clock, sequential_sent_packets)
    
  {
    lemma_CReplicaNextProcessHeartbeat_Pre(s, received_packet);

    var p := CProposerProcessHeartbeat(s.proposer, received_packet, clock, cur_req_set, prev_req_set);
    // var (s', sequential_sent_packets) := 
		// (
		s' :=	s.(
				proposer := p,
				acceptor := CAcceptorProcessHeartbeat(s.acceptor, received_packet)
			);
		sequential_sent_packets := OutboundPacket(None());
		// )
    // ;
    lemma_CReplicaNextProcessHeartbeat(s, received_packet, clock, s', sequential_sent_packets);
    // (s', sequential_sent_packets)
	}


  // /** 9 lines of manual code for I1 */
  // method CReplicaNextProcessHeartbeat(s: CReplica, received_packet: CPacket, clock: int, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s' : CReplica, sequential_sent_packets:OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_Heartbeat?
		 
  //   /** Manually Added for I1 */
  //   requires cur_req_set != prev_req_set
  //   requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
  //   requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
  //   modifies cur_req_set, prev_req_set
  //   ensures  s'.executor == s.executor
  //   ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
  //   ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set

  //   ensures CReplicaIsValid(s') 
  //   && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
  //   && OutboundPacketsIsValid(sequential_sent_packets) 
  //   && LReplicaNextProcessHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), clock, AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	var t1 := 
	// 		CProposerProcessHeartbeat(s.proposer, received_packet, clock, cur_req_set, prev_req_set); 		
	// 	var t2 := 
	// 		CAcceptorProcessHeartbeat(s.acceptor, received_packet); 		
	// 	var t3 := 
	// 		PacketSequence([]); 		
	// 	s' := 
	// 		s.(proposer := t1, acceptor := t2); 
  //   sequential_sent_packets := t3;	
  //   lemma_Postconditions(s, received_packet, s', sequential_sent_packets); /** Manually Added */	
	// 	// (t4, t3)
	// }

  function method CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
		s : CReplica) : (CReplica, OutboundPackets)
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
    requires Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(s)
    ensures 
      var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s);
      Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(
        (AbstractifyCReplicaToLReplica(s)), s', sequential_sent_packets)
  {
		var (t0, t1_0) := CProposerMaybeEnterNewViewAndSend1a(s.proposer); 
    var (s', sequential_sent_packets) := 
		(
			s.(
				proposer := t0
			),
			t1_0
		)
    ;
    lemma_CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s', sequential_sent_packets);
    (s', sequential_sent_packets)
	}

  // function method CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s: CReplica) : (CReplica, OutboundPackets) 
	// 	requires CReplicaIsValid(s)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s); 
  //   CReplicaIsValid(s') 
  //   && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
  //   && OutboundPacketsIsValid(sequential_sent_packets) 
  //   && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	var t1 := 
	// 		CProposerMaybeEnterNewViewAndSend1a(s.proposer); 		
	// 	var t2 := 
	// 		s.(proposer := t1.0);
  //   lemma_NoReceived_Postconditions(s, t2, t1.1); /** Manually Added */	 		
	// 	(t2, t1.1)
	// }

  function method CReplicaNextSpontaneousMaybeEnterPhase2(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterPhase2(s); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextSpontaneousMaybeEnterPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerMaybeEnterPhase2(s.proposer, s.acceptor.log_truncation_point); 		
		var t2 := 
			s.(proposer := t1.0); 		
    lemma_NoReceived_Postconditions(s, t2, t1.1); /** Manually Added */	 	
		(t2, t1.1)
	}

  // function method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica) : (CReplica, OutboundPackets)
  //   requires CReplicaIsValid(s)
  //   ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s);
  //           CReplicaIsValid(s') 
  //           && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
  //           && OutboundPacketsIsValid(sequential_sent_packets) 
  //           && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  // {
  //   // var t1 :=
  //   // if exists opn :: 
  //   //   && opn in s.acceptor.last_checkpointed_operation
  //   //   && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) then
  //   //   var opn :| opn in s.acceptor.last_checkpointed_operation
  //   //             && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
  //   //   if opn > s.acceptor.log_truncation_point then
  //   //     var t1 := CAcceptorTruncateLog(s.acceptor, opn);
  //   //     (
  //   //       s.(acceptor := t1), PacketSequence([])
  //   //     )
  //   //   else
  //   //     (s, PacketSequence([]))         
  //   // else
  //   //     (s, PacketSequence([]));
  //   // lemma_NoReceived_Postconditions(s, t1.0, t1.1);
  //   // (t1.0, t1.1)

  //   var t1 :=
  //   if exists opn :: 
  //     && opn in s.acceptor.last_checkpointed_operation && opn > s.acceptor.log_truncation_point
  //     && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) then
  //     var opn :| opn > s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
  //     // if opn > s.acceptor.log_truncation_point then
  //       var t1 := CAcceptorTruncateLog(s.acceptor, opn);
  //       (
  //         s.(acceptor := t1), PacketSequence([])
  //       )
  //     // else
  //     //   (s, PacketSequence([]))  
  //   else if 
  //     exists opn :: 
  //     && opn in s.acceptor.last_checkpointed_operation && opn <= s.acceptor.log_truncation_point
  //     && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) then
  //       (s, PacketSequence([]))
  //   else
  //       (s, PacketSequence([]));
  //   lemma_NoReceived_Postconditions(s, t1.0, t1.1);
  //   (t1.0, t1.1)
  // }

  function method CReplicaNextSpontaneousMaybeMakeDecision(
		s : CReplica) : (CReplica, OutboundPackets)
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeMakeDecision(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeMakeDecision(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
    requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(s)
    ensures
      var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeMakeDecision(s);
      Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(
        (AbstractifyCReplicaToLReplica(s)), s', sequential_sent_packets)
  {
		var opn := s.executor.ops_complete; 
		
    var (s', sequential_sent_packets) :=
    if  && s.executor.next_op_to_execute.COutstandingOpUnknown? && opn in s.learner.unexecuted_learner_state && |s.learner.unexecuted_learner_state[opn].received_2b_message_senders| >= CMinQuorumSize(s.learner.constants.all.config)
		then 
			(
				s.(
					executor := CExecutorGetDecision(s.executor, s.learner.max_ballot_seen, opn, s.learner.unexecuted_learner_state[opn].candidate_learned_value)
				),
				OutboundPacket(None())
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
    ;

    lemma_CReplicaNextSpontaneousMaybeMakeDecision(s, s', sequential_sent_packets);
    (s', sequential_sent_packets)
	}

  // function method CReplicaNextSpontaneousMaybeMakeDecision(s: CReplica) : (CReplica, OutboundPackets) 
	// 	requires CReplicaIsValid(s)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeMakeDecision(s); 
  //   CReplicaIsValid(s') 
  //   && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
  //   && OutboundPacketsIsValid(sequential_sent_packets) 
  //   && LReplicaNextSpontaneousMaybeMakeDecision(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	var t1 := 
	// 		var opn := 
	// 			s.executor.ops_complete; 			
	// 		var t1 := 
	// 			if s.executor.next_op_to_execute.COutstandingOpUnknown? && opn in s.learner.unexecuted_learner_state && |s.learner.unexecuted_learner_state[opn].received_2b_message_senders| >= CMinQuorumSize(s.learner.constants.all.config) then 
	// 				var t1 := 
	// 					CExecutorGetDecision(s.executor, s.learner.max_ballot_seen, opn, s.learner.unexecuted_learner_state[opn].candidate_learned_value); 					
	// 				var t2 := 
	// 					s.(executor := t1); 					
	// 				var t3 := 
	// 					PacketSequence([]); 					
	// 				(t2, t3) 
	// 			else 
	// 				var t1 := 
	// 					s; 					
	// 				var t2 := 
	// 					PacketSequence([]); 					
	// 				(t1, t2); 			
	// 		(t1.1, t1.0); 		
  //   lemma_NoReceived_Postconditions(s, t1.1, t1.0); /** Manually Added */	 	
	// 	(t1.1, t1.0)
	// }

  method CReplicaNextSpontaneousMaybeExecute(
		s : CReplica,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    requires s.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
    requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(s)
    // requires reply_cache_mutable.Size() < 0x1_0000_0000_0000_0000
    modifies s.executor.app.app
    modifies cur_req_set, prev_req_set, reply_cache_mutable
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set
    ensures MutableMap.MapOf(reply_cache_mutable) == s'.executor.reply_cache

		// ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); 
    ensures CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
    requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(s)
    // ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); 
    ensures Replica_Next_Spontaneous_MaybeExecute_Postconditions(
      (AbstractifyCReplicaToLReplica(s)), s', sequential_sent_packets)
  {
    // var (s', sequential_sent_packets) := 
		if  && s.executor.next_op_to_execute.COutstandingOpKnown? && CLtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) /* && CReplicaConstantsValid(s.executor.constants) */
		{ 
			var v := s.executor.next_op_to_execute.v; 
			// var (t0, t1_1) := CExecutorExecute(s.executor); 
			// (
      var p := CProposerResetViewTimerDueToExecution(s.proposer, s.executor.next_op_to_execute.v, cur_req_set, prev_req_set);
      var e, packets := CExecutorExecute_I1(s.executor, reply_cache_mutable);
			s' := s.(
					proposer := p,
					learner := CLearnerForgetDecision(s.learner, s.executor.ops_complete),
					executor := e
				);
			sequential_sent_packets := packets;
			// )
    }
		else 
    {
			// (
				s' := s;
				sequential_sent_packets := OutboundPacket(None());
			// )
    }
    lemma_CReplicaNextSpontaneousMaybeExecute(s, s', sequential_sent_packets);
    // (s', sequential_sent_packets)
	}


  // /** 15 lines manual code for I1 */
  // method CReplicaNextSpontaneousMaybeExecute(s: CReplica, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
	// 	requires CReplicaIsValid(s)
		
  //   /** Manually Added for I1 */
  //   requires cur_req_set != prev_req_set
  //   requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
  //   requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
  //   requires s.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
  //   modifies cur_req_set, prev_req_set, reply_cache_mutable
  //   ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
  //   ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set
  //   ensures MutableMap.MapOf(reply_cache_mutable) == s'.executor.reply_cache

  //   ensures CReplicaIsValid(s') 
  //   && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
  //   && OutboundPacketsIsValid(sequential_sent_packets) 
  //   && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	// var t1 := 
	// 		if s.executor.next_op_to_execute.COutstandingOpKnown? && CLtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) && CReplicaConstantsValid(s.executor.constants) { 
	// 			// var t1 := 
	// 				var v := 
	// 					s.executor.next_op_to_execute.v; 					
	// 				var t1 := 
	// 					CProposerResetViewTimerDueToExecution(s.proposer, v, cur_req_set, prev_req_set); 					
	// 				var t2 := 
	// 					CLearnerForgetDecision(s.learner, s.executor.ops_complete); 					
	// 				var e, p := 
	// 					CExecutorExecute_I1(s.executor, reply_cache_mutable); /** Invoke I1 method */ 					
	// 				s' := s.(proposer := t1, learner := t2, executor := e); 		
  //         sequential_sent_packets := p;			
	// 				// (t4, t3.1); 				
	// 			// (t1.0, t1.1) 
  //     } else { 
	// 			s' := s; 				
	// 			sequential_sent_packets := PacketSequence([]); 				
	// 			// (t1, t2); 		
  //     }
  //   lemma_NoReceived_Postconditions(s, s', sequential_sent_packets); /** Manually Added */
	// 	// (t1.0, t1.1)
	// }

  function method CReplicaNextReadClockMaybeSendHeartbeat(
		s : CReplica ,
		clock : CClockReading) : (CReplica, OutboundPackets)
		requires CReplicaIsValid(s)
		// requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextReadClockMaybeSendHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))

    requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(s)
    ensures
      var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock);
      Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(
        (AbstractifyCReplicaToLReplica(s)), s', clock, sequential_sent_packets)
  {
    var (s', sequential_sent_packets) := 
		if clock.t < s.nextHeartbeatTime
		then 
			(
				s,
				OutboundPacket(None())
			)
		else 
			(
				s.(
					nextHeartbeatTime := UpperBoundedAdditionImpl(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val)
				),
				// BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete))
        /* 之后要改 */
        Broadcast(
          BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete))
        )
      )
    ;
    lemma_CReplicaNextReadClockMaybeSendHeartbeat(s, clock, s', sequential_sent_packets);
    (s', sequential_sent_packets) 
	}

  // function method CReplicaNextReadClockMaybeSendHeartbeat(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
	// 	requires CReplicaIsValid(s)
	// 	// requires CClockReadingIsValid(clock)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock); 
  //   CReplicaIsValid(s') 
  //   && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
  //   && OutboundPacketsIsValid(sequential_sent_packets) 
  //   && LReplicaNextReadClockMaybeSendHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	var t1 := 
	// 		if clock.t < s.nextHeartbeatTime then 
	// 			var t1 := 
	// 				s; 				
	// 			var t2 := 
	// 				PacketSequence([]); 				
	// 			(t1, t2) 
	// 		else 
	// 			var t1 := 
	// 				UpperBoundedAdditionImpl(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val); 				
	// 			var t2 := 
	// 				Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete))); 				
	// 			var t3 := 
	// 				s.(nextHeartbeatTime := t1); 				
	// 			(t3, t2); 		
  //   lemma_NoReceived_Postconditions(s, t1.0, t1.1); /** Manually Added */
	// 	(t1.0, t1.1)
	// }

  /** 10 lines manual code for I1 */
  method CReplicaNextReadClockCheckForViewTimeout(s: CReplica, clock: CClockReading, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)

    /** Manually Added for I1 */
		requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set
    ensures  s'.executor.reply_cache == s.executor.reply_cache

    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockCheckForViewTimeout(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForViewTimeout(s.proposer, clock.t, cur_req_set, prev_req_set); 		
		sequential_sent_packets := 
			PacketSequence([]); 		
		s' := 
			s.(proposer := t1); 		
    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets); /** Manually Added */
		// (t3, t2)
	}

  method CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s: CReplica, clock: CClockReading, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CReplica, sequential_sent_packets:OutboundPackets) 
		requires CReplicaIsValid(s)
		
    /** Manually Added for I1 */
    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set

    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForQuorumOfViewSuspicions(s.proposer, clock.t, cur_req_set, prev_req_set); 		
		sequential_sent_packets := 
			PacketSequence([]); 		
		s' := 
			s.(proposer := t1); 		
    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets); /** Manually Added */
		// (t3, t2)
	}

  /************************** AutoMan Translation End ************************/

  /************************** Manual Code For I0 ************************/
  /** 3 lines manual code for I1 */
  // method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
  //   requires CReplicaIsValid(s)

  //   /** Manually Added for I1 */
  //   ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
  //   ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
  //   ensures  s'.executor.reply_cache == s.executor.reply_cache

  //   ensures 
  //           CReplicaIsValid(s') 
  //           && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
  //           && OutboundPacketsIsValid(sequential_sent_packets) 
  //           && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  // {
  //   if (exists opn :: opn in s.acceptor.last_checkpointed_operation && opn > s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) )
  //   {
  //       var opn :| opn > s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
  //       var newAcceptor := CAcceptorTruncateLog(s.acceptor, opn);
  //       s' := s.(acceptor := newAcceptor);
  //       sequential_sent_packets := Broadcast(CBroadcastNop);
  //       assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
  //   } 
  //   else 
  //   if (exists opn :: opn in s.acceptor.last_checkpointed_operation && opn <= s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) )
  //   {
  //       s' := s;
  //       sequential_sent_packets := Broadcast(CBroadcastNop);
  //       assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
  //   } 
  //   else {
  //       /** This is a branch that cannot be executed, so we use an axiom lemma to pass the verification */
  //       assert !exists opn :: opn in s.acceptor.last_checkpointed_operation
  //       && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
  //       s' := s;
  //       sequential_sent_packets := Broadcast(CBroadcastNop);
  //       lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
  //       assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
  //   }
  //   lemma_NoReceived_Postconditions(s, s', sequential_sent_packets);
  // }
  
  lemma {:axiom}  lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica, s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures 
            CReplicaIsValid(s') 
            && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
            && OutboundPacketsIsValid(sequential_sent_packets) 
            && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  
  /** 3 lines manual code for I1 */
  method CReplicaNextReadClockMaybeNominateValueAndSend2a(s:CReplica, clock:CClockReading) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockMaybeNominateValueAndSend2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))

    /** Manually Added for I1 */
    ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
    ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
    // ensures  s'.executor.reply_cache == s.executor.reply_cache
  {
    var newProposer, packets := CProposerMaybeNominateValueAndSend2a(s.proposer, clock.t, s.acceptor.log_truncation_point);
    s' := s.(proposer := newProposer);
    sequential_sent_packets := packets;

    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets);
  }
  /************************** Manual Code For I0 End ************************/

  /************************** Manually Optimization for I1 ********************/
  method CGetHighestValueAmongMajority(acceptor:CAcceptor, n:int) returns (opn:COperationNumber)
    requires CAcceptorIsValid(acceptor)
    requires 0 < n as int <= |acceptor.last_checkpointed_operation|
    ensures  IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySeq(acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), n as int)
    // requires |acceptor.last_checkpointed_operation| > n as int
  {
      // var i:int := 1;
      var cm := acceptor.last_checkpointed_operation;
      var a := SeqToArray(cm);
      assert multiset(a[..]) == multiset(cm);
      SortSeq(a);

      ghost var s := a[..]; 
      assert multiset(s) == multiset(cm);
      forall i, j | 0 <= i < j < |s|
        ensures s[i] <= s[j]
      {
        assert a[i] <= a[j];
      }

      opn := a[a.Length - (n as int)];

      assert opn == s[|s|-(n as int)];

      ghost var f1 := (x:COperationNumber) => x > s[|s|-(n as int)];
      ghost var f2 := (x:COperationNumber) => x > opn;
      Lemma_CountMatchesInSeqSameForSameFunctions(s, f1, f2);
      ghost var f1' := (x:COperationNumber) => x >= s[|s|-(n as int)];
      ghost var f2' := (x:COperationNumber) => x >= opn;
      Lemma_CountMatchesInSeqSameForSameFunctions(s, f1', f2');

      lemma_SortedSequenceMatchCount(s, n as int);
      assert IsNthHighestValueInSequence(opn, s, n);
      lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, s, multiset(cm), n);
      lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, cm, multiset(cm), n);
      lemma_AbstractionOfCOperationNumberIsNthHighestValueInSequence(opn, cm, n);
  }


  predicate Sorted_COperationNumber(a: array<COperationNumber>, low: uint64, high: uint64)
    requires a.Length < 0xFFFFFFFFFFFFFFFF
    requires 0 <= low <= high <= a.Length as uint64
    reads a
  {
    forall i, j :: low <= i < j < high ==> a[i] <= a[j]
  }

  predicate NeighborSorted_COperationNumber(a: array<COperationNumber>, low: uint64, high: uint64)
    requires a.Length < 0xFFFFFFFFFFFFFFFF
    requires 0 <= low <= high <= a.Length as uint64
    reads a
  {
    forall i {:trigger a[i-1], a[i]} :: low < i < high ==> a[i-1] <= a[i]
  }

  lemma lemma_NeighborSortedImpliesSortedCOperationNumber(a: array<COperationNumber>, low: uint64, high: uint64)
    requires a.Length < 0xFFFFFFFFFFFFFFFF
    requires 0 <= low <= high <= a.Length as uint64
    requires NeighborSorted_COperationNumber(a, low, high)
    ensures Sorted_COperationNumber(a, low, high)
    decreases high - low
  {
    if low != high {
      lemma_NeighborSortedImpliesSortedCOperationNumber(a, low+1, high);
      forall j | low < j < high
        ensures  a[low] <= a[j]
      {
        var i := low+1;
        if(i == j) {
          assert a[j-1] <= a[j];
        } else {
          assert a[i-1] <= a[i];
          assert a[i] <= a[j];
          assert a[low] <= a[j];
        }
      }
    }
  }

  method SortSeq(a : array<COperationNumber>)
      modifies a
      requires a.Length < 0xFFFFFFFFFFFFFFFF
      ensures Sorted_COperationNumber(a, 0, a.Length as uint64)
      ensures multiset(a[..]) == old(multiset(a[..]))
  {
      if a.Length as uint64 == 0 { return; }
      var i:uint64 := 1;
      while i < a.Length as uint64
          invariant 0 < i <= a.Length as uint64
          invariant NeighborSorted_COperationNumber(a, 0, i)
          invariant multiset(a[..]) == old(multiset(a[..]))
      {
          var j:uint64 := i;
          while 0 < j && a[j-1] > a[j]
          invariant 0 <= j <= i
          invariant NeighborSorted_COperationNumber(a, 0, j)
          invariant NeighborSorted_COperationNumber(a, j, i+1)
          invariant 0 < j < i ==> a[j-1] <= a[j+1]
          invariant multiset(a[..]) == old(multiset(a[..]))
          {
          // The proof of correctness uses the totality property here.
          // It implies that if two elements are not previously in
          // sorted order, they will be after swapping them.
              a[j], a[j-1] := a[j-1], a[j];
              j := j - 1;
          }
          i := i + 1;
      }
      lemma_NeighborSortedImpliesSortedCOperationNumber(a, 0, a.Length as uint64);
  }

  method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) 
    ensures LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
    ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions((AbstractifyCReplicaToLReplica(s)),
                                                                                   s', sequential_sent_packets)
    ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
    ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
    ensures  s'.executor.reply_cache == s.executor.reply_cache
  {
    ghost var ss := AbstractifyCReplicaToLReplica(s);
    var n := CMinQuorumSize(s.constants.all.config);
    assert n <= |s.constants.all.config.replica_ids|;
    assert |s.acceptor.constants.all.config.replica_ids| == |s.acceptor.last_checkpointed_operation|;
    assert s.constants == s.acceptor.constants;
    assert |s.constants.all.config.replica_ids| == |s.acceptor.last_checkpointed_operation|;

    var opn := CGetHighestValueAmongMajority(s.acceptor, n);
    
    // var opn := ComputeNthHighestValueSeq(s.acceptor.last_checkpointed_operation, n);
    // assert CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) == 
    //         IsLogTruncationPointValid(
    //       opn as int,
    //       AbstractifySeq(s.acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber),
    //       AbstractifyCConfigurationToLConfiguration(s.constants.all.config)
    //     );

    assert IsLogTruncationPointValid(
          AbstractifyCOperationNumberToOperationNumber(opn),
          AbstractifySeq(s.acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber),
          AbstractifyCConfigurationToLConfiguration(s.constants.all.config)
        );
    assert AbstractifyCOperationNumberToOperationNumber(opn) == opn as int;
    assert AbstractifySeq(s.acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber) == ss.acceptor.last_checkpointed_operation;
    assert AbstractifyCConfigurationToLConfiguration(s.constants.all.config) == ss.constants.all.config;
    assert IsLogTruncationPointValid(opn as int, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);

    if opn > s.acceptor.log_truncation_point { 
        // ghost var op :| op in ss.acceptor.last_checkpointed_operation && IsLogTruncationPointValid(op, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);
        var newAcceptor := CAcceptorTruncateLog(s.acceptor, opn);
        s' := s.(acceptor := newAcceptor);
        sequential_sent_packets := Broadcast(CBroadcastNop);

        // assert opn as int == op;
        // ghost var opp := opn as int;
        // assert opp in ss.acceptor.last_checkpointed_operation;
        // assert IsLogTruncationPointValid(opp, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);
        // assert opp in ss.acceptor.last_checkpointed_operation && IsLogTruncationPointValid(opp, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);
        // assert CReplicaIsValid(s');
        // assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
        //     AbstractifyCReplicaToLReplica(s),
        //     AbstractifyCReplicaToLReplica(s'),
        //     AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    }
    else {
        s' := s;
        sequential_sent_packets := Broadcast(CBroadcastNop);
    }
    lamme_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
  }

  /************************** Manually Optimization for I1 End ********************/

  predicate ConstantsStayConstant_Replica(replica:LReplica, replica':CReplica)
    requires CReplicaConstantsIsAbstractable(replica'.constants)
  {
    && AbstractifyCReplicaConstantsToLReplicaConstants(replica'.constants) == replica.constants
    && replica.constants == replica.proposer.constants
    && replica.constants == replica.acceptor.constants
    && replica.constants == replica.learner.constants
    && replica.constants == replica.executor.constants
    && replica'.constants == replica'.proposer.constants
    && replica'.constants == replica'.acceptor.constants
    && replica'.constants == replica'.learner.constants
    && replica'.constants == replica'.executor.constants
  }

  /********* pre conditions *******************/
  predicate Replica_Common_Preconditions(replica:CReplica, inp:CPacket)
  {
    && CReplicaIsValid(replica)
    && CPacketIsSendable(inp)
  }

  predicate Replica_Next_Process_Heartbeat_Preconditions(replica:CReplica, inp:CPacket)
  {
    /*
    && Replica_Common_Preconditions(replica, inp)
    && NextCAcceptor_ProcessHeartbeatPreconditions(replica.acceptor, inp.msg, inp.src)
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_Heartbeat?
    */

    && inp.msg.CMessage_Heartbeat?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_MaybeEnterPhase2_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_Process_Request_Preconditions(replica:CReplica, inp:CPacket)
  {
    /*
    && Replica_Common_Preconditions(replica, inp)
    && CProposerIsValid(replica.proposer)
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_Request?
    */

    && inp.msg.CMessage_Request?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_1a_Preconditions(replica:CReplica, inp:CPacket)
  {
    /*
    && Replica_Common_Preconditions(replica, inp)
    && NextCAcceptor_Phase1Preconditions(replica.acceptor, inp.msg, inp.src)
    */

    && inp.msg.CMessage_1a?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_1b_Preconditions(replica:CReplica, inp:CPacket)
  {
    /*
    && Replica_Common_Preconditions(replica, inp)
    && CProposerIsValid(replica.proposer)
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_1b?
    */

    && inp.msg.CMessage_1b?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_StartingPhase2_Preconditions(replica:CReplica, inp:CPacket)
  {
    /*
    && Replica_Common_Preconditions(replica, inp)
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_StartingPhase2?
    */

    && inp.msg.CMessage_StartingPhase2?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_2a_Preconditions(replica:CReplica, inp:CPacket)
  {
    /*
    && Replica_Common_Preconditions(replica, inp)
    && NextCAcceptor_Phase2Preconditions_AlwaysEnabled(replica.acceptor, inp.msg, inp.src)
    */

    && inp.msg.CMessage_2a?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_2b_Preconditions(replica:CReplica, inp:CPacket)
  {
    /*
    && Replica_Common_Preconditions(replica, inp)
    && LearnerState_Process2b__Preconditions(replica.learner, replica.executor, inp)
    */

    && inp.msg.CMessage_2b?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_AppStateRequest_Preconditions(replica:CReplica, inp:CPacket)
  {
    /*
    && Replica_Common_Preconditions(replica, inp)
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_AppStateRequest?
    */

    && inp.msg.CMessage_AppStateRequest?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_AppStateSupply_Preconditions(replica:CReplica, inp:CPacket)
  {
    /*
    && Replica_Common_Preconditions(replica, inp)
    && inp.msg.CMessage_AppStateSupply?
    && LearnerState_ForgetOperationsBefore__Preconditions(replica.learner, inp.msg.opn_state_supply)
    */

    && inp.msg.CMessage_AppStateSupply?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  /************** post conditions *********************/

  predicate Replica_Common_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket, packets_sent:OutboundPackets)
  {
    && CReplicaConstantsIsValid(replica'.constants)
    && CPacketIsSendable(inp)
    && CReplicaIsAbstractable(replica')
    && ConstantsStayConstant_Replica(replica, replica')
    && CReplicaIsValid(replica')
    && OutboundPacketsIsValid(packets_sent)
    && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
    && OutboundPacketsIsAbstractable(packets_sent)
  }

    predicate Replica_Common_Postconditions_NoPacket(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
  {
    && CReplicaConstantsIsValid(replica'.constants)
    && CReplicaIsAbstractable(replica')
    && ConstantsStayConstant_Replica(replica, replica')
    && CReplicaIsValid(replica')
    && OutboundPacketsIsValid(packets_sent)
    && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
    && OutboundPacketsIsAbstractable(packets_sent)
  }

  predicate Replica_Next_Process_AppStateSupply_Postconditions(replica:LReplica, replica':CReplica,
                                                               inp:CPacket, packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_AppStateSupply?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcessAppStateSupply(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))

    /*
    && CPacketIsValid(inp)
    && CPacketIsAbstractable(inp)

    && CReplicaIsValid(replica')
    && CReplicaIsAbstractable(replica')
  
    && OutboundPacketsIsValid(packets_sent)
    && OutboundPacketsIsAbstractable(packets_sent)

    && inp.msg.CMessage_AppStateSupply?
    && CReplicaConstantsIsValid(replica'.constants)
    && CPacketIsSendable(inp)

    && ConstantsStayConstant_Replica(replica, replica')
    && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])

    && LReplicaNextProcessAppStateSupply(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
    */
  }

  predicate Replica_Next_Process_AppStateRequest_Postconditions(replica:LReplica, replica':CReplica,
                                                                inp:CPacket, packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_AppStateRequest?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcessAppStateRequest(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))

    /*
    && inp.msg.CMessage_AppStateRequest?
    && CMessageIsMarshallable(inp.msg)
    && ConstantsStayConstant_Replica(replica, replica')
    && OutboundPacketsHasCorrectSrc(
      packets_sent, 
      replica'.constants.all.config.replica_ids[replica'.constants.my_index])

    && CReplicaIsValid(replica')
    && CPacketIsValid(inp)
    && OutboundPacketsIsValid(packets_sent)
    && LReplicaNextProcessAppStateRequest(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
    */
  }

  predicate Replica_Next_Process_2b_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                   packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_2b?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcess2b(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))

    /*
    && inp.msg.CMessage_2b?
    && CMessageIsMarshallable(inp.msg)
    && ConstantsStayConstant_Replica(replica, replica')
    && OutboundPacketsHasCorrectSrc(
      packets_sent, 
      replica'.constants.all.config.replica_ids[replica'.constants.my_index])

    && CReplicaIsValid(replica')
    && CPacketIsValid(inp)
    && OutboundPacketsIsValid(packets_sent)
    && LReplicaNextProcess2b(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
    */
  }

  predicate Replica_Next_Process_2a_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                   packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_2a?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcess2a(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_StartingPhase2_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                               packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_StartingPhase2?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcessStartingPhase2(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_1b_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                   packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_1b?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcess1b(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_1a_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                   packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_1a?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcess1a(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_Request_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                        packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    // run-time error
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_Request?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)

    // refinement
    && LReplicaNextProcessRequest(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate ReplicaCommonPostconditions(replica:LReplica, replica':CReplica, sent_packets:OutboundPackets)
  {
    && CReplicaConstantsIsValid(replica'.constants)
    && AbstractifyCReplicaConstantsToLReplicaConstants(replica'.constants) == replica.constants
    && CReplicaIsAbstractable(replica')
    && CReplicaIsValid(replica')
    && OutboundPacketsIsValid(sent_packets)
    && OutboundPacketsIsAbstractable(sent_packets)
    && OutboundPacketsHasCorrectSrc(sent_packets, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
  }

  predicate Replica_Next_Process_Heartbeat_Postconditions(replica:LReplica, replica':CReplica,
                                                          inp:CPacket, clock:int, packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_Heartbeat?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcessHeartbeat(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         clock as int,
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }



  predicate Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(
    replica:LReplica,
    replica':CReplica,
    clock:CClockReading,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextReadClockMaybeNominateValueAndSend2a(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCClockReadingToClockReading(clock),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(
    replica:LReplica,
    replica':CReplica,
    clock:CClockReading,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextReadClockCheckForViewTimeout(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCClockReadingToClockReading(clock),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(
    replica:LReplica,
    replica':CReplica,
    clock:CClockReading,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCClockReadingToClockReading(clock),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(
    replica:LReplica,
    replica':CReplica,
    clock:CClockReading,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextReadClockMaybeSendHeartbeat(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCClockReadingToClockReading(clock),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_MaybeEnterPhase2_Postconditions(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeEnterPhase2(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeMakeDecision(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica:LReplica, replica':CReplica,
                                                                 packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeExecute(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  /* ----------------------------------------- */

  /* ------------ Manually Written for I0 ------- */

lemma lemma_SortedSequenceMatchCount(s:seq<COperationNumber>, k:int)
  requires |s| > 0
  requires 0 < k <= |s|
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures CountMatchesInSeq(s, (x:COperationNumber) => x > s[|s|-k]) < k
  ensures CountMatchesInSeq(s, (x:COperationNumber) => x >= s[|s|-k]) >= k
{
  var s' := s[1..];
  var f1 := (x:COperationNumber) => x > s[|s|-k];
  var f2 := (x:COperationNumber) => x >= s[|s|-k];

  if k == |s|
  {
    calc {
      CountMatchesInSeq(s, f1);
      CountMatchesInSeq(s', f1);
      < { Lemma_CountMatchesInSeqBounds(s', f1); }
      k;
    }

    Lemma_CountMatchesInSeqAll(s, f2);
  }
  else
  {
    var f1' := (x:COperationNumber) => x > s'[|s'|-k];
    var f2' := (x:COperationNumber) => x >= s'[|s'|-k];
    lemma_SortedSequenceMatchCount(s', k);
    assert s'[|s'|-k] == s[|s|-k];

    calc {
      CountMatchesInSeq(s, f1);
      CountMatchesInSeq(s', f1);
        { Lemma_CountMatchesInSeqSameForSameFunctions(s', f1, f1'); }
      CountMatchesInSeq(s', f1');
      < k;
    }

    calc {
      CountMatchesInSeq(s, f2);
      >= CountMatchesInSeq(s', f2);
        { Lemma_CountMatchesInSeqSameForSameFunctions(s', f2, f2'); }
      CountMatchesInSeq(s', f2');
      >= k;
    }
  }
}

predicate IsNthHighestValueInMultisetOfCOperationNumbers(v:COperationNumber, m:multiset<COperationNumber>, n:int)
{
  && 0 < n as int <= |m|
  && v in m
  && CountMatchesInMultiset(m, (x:COperationNumber) => x > v) < n as int
  && CountMatchesInMultiset(m, (x:COperationNumber) => x >= v) >= n as int
}

lemma lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(v:COperationNumber, s:seq<COperationNumber>, m:multiset<COperationNumber>, n:int)
  requires m == multiset(s)
  ensures  IsNthHighestValueInSequence(v, s, n) <==> IsNthHighestValueInMultisetOfCOperationNumbers(v, m, n)
{
  Lemma_MatchCountInSeqIsMatchCountInMultiset(s, m, (x:COperationNumber) => x > v);
  Lemma_MatchCountInSeqIsMatchCountInMultiset(s, m, (x:COperationNumber) => x >= v);
}

lemma lemma_AbstractionOfCOperationNumberIsNthHighestValueInSequence(opn:COperationNumber, cm:seq<COperationNumber>, n:int)
  requires IsNthHighestValueInSequence(opn, cm, n)
  ensures  IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySeq(cm, AbstractifyCOperationNumberToOperationNumber), n as int)
{
  var f1 := (x:COperationNumber) => x > opn;
  var f2 := x => x > AbstractifyCOperationNumberToOperationNumber(opn);
  Lemma_CountMatchesInSeqCorrespondence(cm, f1, AbstractifySeq(cm, AbstractifyCOperationNumberToOperationNumber), f2);

  var f1' := (x:COperationNumber) => x >= opn;
  var f2' := x => x >= AbstractifyCOperationNumberToOperationNumber(opn);
  Lemma_CountMatchesInSeqCorrespondence(cm, f1', AbstractifySeq(cm, AbstractifyCOperationNumberToOperationNumber), f2');
}

method ComputeNthHighestValueSeq(cm:seq<COperationNumber>, n:int) returns (opn:COperationNumber)
  // requires CLastCheckpointedMapIsAbstractable(cm)
  requires SeqIsAbstractable(cm,AbstractifyCOperationNumberToOperationNumber)
  requires 0 < n <= |cm|
  // requires |cm| < 0xffff_ffff_ffff_ffff
  ensures  IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySeq(cm, AbstractifyCOperationNumberToOperationNumber), n as int)
{
  var a := InsertSort(cm);
  assert multiset(a[..]) == multiset(cm);
  assert |a| == |cm|;
  ghost var s := a[..]; 
  opn := a[|a|-(n as int)];
  assert opn == s[|s|-(n as int)];

  lemma_SortedSequenceMatchCount(s, n as int);
  assert IsNthHighestValueInSequence(opn, s, n);
  lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, s, multiset(cm), n);
  lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, cm, multiset(cm), n);
  lemma_AbstractionOfCOperationNumberIsNthHighestValueInSequence(opn, cm, n);
}


  /* ----------------------------------------- */
  lemma {:axiom} lemma_NoReceived_Postconditions(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires CReplicaIsAbstractable(replica)
    ensures Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(replica), replica', packets_sent)

  lemma {:axiom} lemma_Postconditions(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires CReplicaIsAbstractable(replica)
    ensures Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(replica), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaInit(constants:CReplicaConstants, replica:CReplica)
    requires CReplicaConstantsIsValid(constants)
    ensures CReplicaIsValid(replica)
    ensures replica.constants == constants
    ensures LReplicaInit(AbstractifyCReplicaToLReplica(replica), AbstractifyCReplicaConstantsToLReplicaConstants(constants))

  lemma {:axiom} lemma_CReplicaNextProcessRequest_pre(replica:CReplica, inp:CPacket)
    requires Replica_Next_Process_Request_Preconditions(replica, inp)
    ensures  inp.src in replica.proposer.constants.all.config.replica_ids

  // lemma {:axiom} lemma_CReplicaNextProcessRequest(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_Process_Request_Preconditions(replica, inp)
  //   ensures  Replica_Next_Process_Request_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
  //                                                        inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcess1a_pre(replica:CReplica, inp:CPacket)
    requires Replica_Next_Process_1a_Preconditions(replica, inp)
    ensures CBallotIsValid(inp.msg.bal_1a)

  lemma {:axiom} lemma_CReplicaNextProcess1a(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_1a_Preconditions(replica, inp)
    ensures Replica_Next_Process_1a_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcess1b(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_1b_Preconditions(replica, inp)
    ensures  Replica_Next_Process_1b_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcessStartingPhase2(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_StartingPhase2_Preconditions(replica, inp)
    ensures Replica_Next_Process_StartingPhase2_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcess2a(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_2a_Preconditions(replica, inp)
    ensures  Replica_Next_Process_2a_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcess2b_pre(replica:CReplica, inp:CPacket)
    requires Replica_Next_Process_2b_Preconditions(replica, inp)
    ensures CBallotIsValid(inp.msg.bal_2b)

  lemma {:axiom} lemma_CReplicaNextProcess2b(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_2b_Preconditions(replica, inp)
    ensures Replica_Next_Process_2b_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcessAppStateSupply(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_AppStateSupply_Preconditions(replica, inp)
    ensures  Replica_Next_Process_AppStateSupply_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcessAppStateRequest(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_AppStateRequest_Preconditions(replica, inp)
    ensures  Replica_Next_Process_AppStateRequest_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                 inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcessHeartbeat_Pre(replica:CReplica, inp:CPacket)
    requires CReplicaIsValid(replica)
    requires inp.msg.CMessage_Heartbeat?
    ensures inp.src in replica.proposer.constants.all.config.replica_ids
    ensures CBallotIsValid(inp.msg.bal_heartbeat)

  lemma {:axiom} lemma_CReplicaNextProcessHeartbeat(replica:CReplica, inp:CPacket, clock:int, replica':CReplica, packets_sent:OutboundPackets)
    requires CReplicaIsValid(replica)
    requires inp.msg.CMessage_Heartbeat?
    ensures Replica_Next_Process_Heartbeat_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                          inp, clock, packets_sent)
    ensures  replica'.executor == replica.executor

  lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica)
    ensures Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                   packets_sent)

  lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeEnterPhase2(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_MaybeEnterPhase2_Preconditions(replica)
    ensures Replica_Next_MaybeEnterPhase2_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', packets_sent)

  lemma {:axiom} lemma_CReplicaNextReadClockMaybeNominateValueAndSend2a(replica:CReplica, clock:CClockReading, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica)
    ensures Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions((AbstractifyCReplicaToLReplica(replica)),
                                                                              replica', clock, packets_sent)

  method SeqToArray<T(0)>(s:seq<T>) returns (a:array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> s[i] == a[i]
    ensures a[..] == s
    ensures fresh(a)
  {
    a := new T[|s|];

    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < i ==> s[j] == a[j]
    {
      a[i] := s[i];
      i := i + 1;
    }
  }

  lemma {:axiom} lamme_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica)
    ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions((AbstractifyCReplicaToLReplica(replica)),
                                                                                   replica', packets_sent)

  lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeMakeDecision(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica)
    ensures  Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                       packets_sent)
    ensures  replica' == replica



  lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeExecute(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica)
    ensures  Replica_Next_Spontaneous_MaybeExecute_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                  packets_sent)

  lemma {:axiom} lemma_CReplicaNextReadClockMaybeSendHeartbeat(replica:CReplica, clock:CClockReading, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica)
    ensures Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                     clock, packets_sent)


  lemma {:axiom} lemma_CReplicaNextReadClockCheckForViewTimeout(replica:CReplica, clock:CClockReading, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica)
    ensures  Replica_Next_ReadClock_CheckForViewTimeout_Postconditions((AbstractifyCReplicaToLReplica(replica)),
                                                                       replica', clock, packets_sent)

  lemma {:axiom} lemma_CReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica:CReplica, clock:CClockReading, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica)
    ensures  Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions((AbstractifyCReplicaToLReplica(replica)),
                                                                                  replica', clock, packets_sent)


}