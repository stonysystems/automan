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
// import opened LiveRSL__ElectionState_i
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
    reads    s.executor.app.app
    // requires CReplicaIsValid(s)
	{
		LReplica(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.nextHeartbeatTime, AbstractifyCProposerToLProposer(s.proposer), AbstractifyCAcceptorToLAcceptor(s.acceptor), AbstractifyCLearnerToLLearner(s.learner), AbstractifyCExecutorToLExecutor(s.executor))
	}

  method CReplicaInit(c: CReplicaConstants) returns (r:CReplica)
		requires CReplicaConstantsIsValid(c)
		// requires CWellFormedLConfiguration(c.all.config)
		// ensures var r := CReplicaInit(c); 
    ensures CReplicaIsValid(r) && LReplicaInit(AbstractifyCReplicaToLReplica(r), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			0; 		
		var t3 := 
			CProposerInit(c); 		
		var t4 := 
			CAcceptorInit(c); 		
		var t5 := 
			CLearnerInit(c); 		
		var t6 := 
			CExecutorInit(c); 		
		r := CReplica(t1, t2, t3, t4, t5, t6);
	}

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

  function method CReplicaNextProcessRequest(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Request?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sequential_sent_packets) 
      && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if received_packet.src in s.executor.reply_cache && s.executor.reply_cache[received_packet.src].CReply? && received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno then 
				var t1 := 
					CExecutorProcessRequest(s.executor, received_packet); 				
				var t2 := 
					s; 				
				(t2, t1) 
			else 
				var t1 := 
					CProposerProcessRequest(s.proposer, received_packet); 				
				var t2 := 
					PacketSequence([]); 				
				var t3 := 
					s.(proposer := t1); 				
				(t3, t2); 		
    lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */
		(t1.0, t1.1)
	}

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

  function method CReplicaNextProcess2a(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2a?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess2a(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcess2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			var m := 
				received_packet.msg; 			
			var t1 := 
				if received_packet.src in s.acceptor.constants.all.config.replica_ids && CBalLeq(s.acceptor.max_bal, m.bal_2a) && CLeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val) then 
					var t1 := 
						CAcceptorProcess2a(s.acceptor, received_packet); 					
					var t2 := 
						s.(acceptor := t1.0); 					
					(t2, t1.1) 
				else 
					var t1 := 
						s; 					
					var t2 := 
						PacketSequence([]); 					
					(t1, t2); 			
			(t1.0, t1.1); 		
    lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */	
		(t1.0, t1.1)
	}

  function method CReplicaNextProcess2b(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2b?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess2b(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcess2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			var opn := 
				received_packet.msg.opn_2b; 			
			var t1 := 
				var op_learnable := 
					(s.executor.ops_complete < opn) || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.COutstandingOpUnknown?); 				
				var t1 := 
					if op_learnable then 
						var t1 := 
							CLearnerProcess2b(s.learner, received_packet); 						
						var t2 := 
							PacketSequence([]); 						
						var t3 := 
							s.(learner := t1); 						
						(t3, t2) 
					else 
						var t1 := 
							s; 						
						var t2 := 
							PacketSequence([]); 						
						(t1, t2); 				
				(t1.0, t1.1); 			
			(t1.0, t1.1); 	
    lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */		
		(t1.0, t1.1)
	}

  function method CReplicaNextProcessReply(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Reply?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessReply(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessReply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			PacketSequence([]); 		
		var t2 := 
			s; 		
    lemma_Postconditions(s, received_packet, t2, t1); /** Manually Added */	
		(t2, t1)
	}

  method CReplicaNextProcessAppStateSupply(s: CReplica, received_packet: CPacket) returns (s':CReplica, sequential_sent_packets:OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateSupply?
		// ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateSupply(s, received_packet); 
    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessAppStateSupply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		// var t1 := 
			if received_packet.src in s.executor.constants.all.config.replica_ids && received_packet.msg.opn_state_supply > s.executor.ops_complete { 
				var t1 := 
					CLearnerForgetOperationsBefore(s.learner, received_packet.msg.opn_state_supply); 				
				var t2 := 
					CExecutorProcessAppStateSupply(s.executor, received_packet); 				
				sequential_sent_packets := 
					PacketSequence([]); 				
				s' := 
					s.(learner := t1, executor := t2); 				
				// (t4, t3) 
      } else { 
				s' := 
					s; 				
				sequential_sent_packets := 
					PacketSequence([]); 
      }				
				// (t1, t2); 		
    lemma_Postconditions(s, received_packet, s', sequential_sent_packets); /** Manually Added */
		// (t1.0, t1.1)
	}

  method CReplicaNextProcessAppStateRequest(s: CReplica, received_packet: CPacket) returns (s':CReplica, sequential_sent_packets:OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateRequest?
		// ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateRequest(s, received_packet); 
    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessAppStateRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1, t2 := 
			CExecutorProcessAppStateRequest(s.executor, received_packet); 		
		s' := 
			s.(executor := t1); 
    sequential_sent_packets:= t2;
    lemma_Postconditions(s, received_packet, s', t2); /** Manually Added */
		// (t2, t1.1)
	}

  function method CReplicaNextProcessHeartbeat(s: CReplica, received_packet: CPacket, clock: int) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Heartbeat?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessHeartbeat(s, received_packet, clock); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), clock, AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerProcessHeartbeat(s.proposer, received_packet, clock); 		
		var t2 := 
			CAcceptorProcessHeartbeat(s.acceptor, received_packet); 		
		var t3 := 
			PacketSequence([]); 		
		var t4 := 
			s.(proposer := t1, acceptor := t2); 	
    lemma_Postconditions(s, received_packet, t4, t3); /** Manually Added */	
		(t4, t3)
	}

  function method CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerMaybeEnterNewViewAndSend1a(s.proposer); 		
		var t2 := 
			s.(proposer := t1.0);
    lemma_NoReceived_Postconditions(s, t2, t1.1); /** Manually Added */	 		
		(t2, t1.1)
	}

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

  

  function method CReplicaNextSpontaneousMaybeMakeDecision(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeMakeDecision(s); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextSpontaneousMaybeMakeDecision(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			var opn := 
				s.executor.ops_complete; 			
			var t1 := 
				if s.executor.next_op_to_execute.COutstandingOpUnknown? && opn in s.learner.unexecuted_learner_state && |s.learner.unexecuted_learner_state[opn].received_2b_message_senders| >= CMinQuorumSize(s.learner.constants.all.config) then 
					var t1 := 
						CExecutorGetDecision(s.executor, s.learner.max_ballot_seen, opn, s.learner.unexecuted_learner_state[opn].candidate_learned_value); 					
					var t2 := 
						s.(executor := t1); 					
					var t3 := 
						PacketSequence([]); 					
					(t2, t3) 
				else 
					var t1 := 
						s; 					
					var t2 := 
						PacketSequence([]); 					
					(t1, t2); 			
			(t1.1, t1.0); 		
    lemma_NoReceived_Postconditions(s, t1.1, t1.0); /** Manually Added */	 	
		(t1.1, t1.0)
	}

  method CReplicaNextSpontaneousMaybeExecute(s: CReplica) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)
		// ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); 
    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		// var t1 := 
			if s.executor.next_op_to_execute.COutstandingOpKnown? && CLtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) && CReplicaConstantsValid(s.executor.constants) { 
				// var t1 := 
					var v := 
						s.executor.next_op_to_execute.v; 					
					var t1 := 
						CProposerResetViewTimerDueToExecution(s.proposer, v); 					
					var t2 := 
						CLearnerForgetDecision(s.learner, s.executor.ops_complete); 					
					var t3, t4 := 
						CExecutorExecute(s.executor); 					
					s':= 
						s.(proposer := t1, learner := t2, executor := t3); 	
          sequential_sent_packets := t4;
				// 	(t4, t3.1); 				
				// (t1.0, t1.1) 
      } else { 
				s' := 
					s; 				
				sequential_sent_packets := 
					PacketSequence([]); 				
				// (t1, t2); 		
      }
    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets); /** Manually Added */
		// (t1.0, t1.1)
	}

  function method CReplicaNextReadClockMaybeSendHeartbeat(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		// requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockMaybeSendHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if clock.t < s.nextHeartbeatTime then 
				var t1 := 
					s; 				
				var t2 := 
					PacketSequence([]); 				
				(t1, t2) 
			else 
				var t1 := 
					UpperBoundedAdditionImpl(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val); 				
				var t2 := 
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete))); 				
				var t3 := 
					s.(nextHeartbeatTime := t1); 				
				(t3, t2); 		
    lemma_NoReceived_Postconditions(s, t1.0, t1.1); /** Manually Added */
		(t1.0, t1.1)
	}

  function method CReplicaNextReadClockCheckForViewTimeout(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		// requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForViewTimeout(s, clock); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockCheckForViewTimeout(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForViewTimeout(s.proposer, clock.t); 		
		var t2 := 
			PacketSequence([]); 		
		var t3 := 
			s.(proposer := t1); 		
    lemma_NoReceived_Postconditions(s, t3, t2); /** Manually Added */
		(t3, t2)
	}

  function method CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		// requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, clock); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForQuorumOfViewSuspicions(s.proposer, clock.t); 		
		var t2 := 
			PacketSequence([]); 		
		var t3 := 
			s.(proposer := t1); 		
    lemma_NoReceived_Postconditions(s, t3, t2); /** Manually Added */
		(t3, t2)
	}

  /************************** AutoMan Translation End ************************/

  /************************** Manual Code For I0 ************************/
  method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures 
            CReplicaIsValid(s') 
            && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
            && OutboundPacketsIsValid(sequential_sent_packets) 
            && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  {
    if (exists opn :: opn in s.acceptor.last_checkpointed_operation && opn > s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) )
    {
        var opn :| opn > s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
        var newAcceptor := CAcceptorTruncateLog(s.acceptor, opn);
        s' := s.(acceptor := newAcceptor);
        sequential_sent_packets := Broadcast(CBroadcastNop);
        assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    } 
    else 
    if (exists opn :: opn in s.acceptor.last_checkpointed_operation && opn <= s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) )
    {
        s' := s;
        sequential_sent_packets := Broadcast(CBroadcastNop);
        assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    } 
    else {
        /** This is a branch that cannot be executed, so we use an axiom lemma to pass the verification */
        assert !exists opn :: opn in s.acceptor.last_checkpointed_operation
        && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
        s' := s;
        sequential_sent_packets := Broadcast(CBroadcastNop);
        lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
        assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    }
    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets);
  }
  
  lemma {:axiom}  lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica, s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures 
            CReplicaIsValid(s') 
            && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
            && OutboundPacketsIsValid(sequential_sent_packets) 
            && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  
  /* 没有更换是因为调用的method还没有被修改成function method */
  method CReplicaNextReadClockMaybeNominateValueAndSend2a(s:CReplica, clock:CClockReading) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockMaybeNominateValueAndSend2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  {
    var newProposer, packets := CProposerMaybeNominateValueAndSend2a(s.proposer, clock.t, s.acceptor.log_truncation_point);
    s' := s.(proposer := newProposer);
    sequential_sent_packets := packets;

    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets);
  }
  /************************** Manual Code For I0 End ************************/


  /* ----------------------------------------- */

	// datatype CReplica = 
	// CReplica
	// (
	// 	constants : CReplicaConstants ,
	// 	nextHeartbeatTime : int ,
	// 	proposer : CProposer ,
	// 	acceptor : CAcceptor ,
	// 	learner : CLearner ,
	// 	executor : CExecutor
	// )

	// predicate CReplicaIsValid(
	// 	s : CReplica)
		
	// {
	// 	CReplicaIsAbstractable(s)
	// 	&&
	// 	CReplicaConstantsIsValid(s.constants)
	// 	&&
	// 	CProposerIsValid(s.proposer)
	// 	&&
	// 	CAcceptorIsValid(s.acceptor)
	// 	&&
	// 	CLearnerIsValid(s.learner)
	// 	&&
	// 	CExecutorIsValid(s.executor)
  //   && 
  //   s.constants == s.acceptor.constants
	// }

	// predicate CReplicaIsAbstractable(
	// 	s : CReplica)
		
	// {
	// 	CReplicaConstantsIsAbstractable(s.constants)
	// 	&&
	// 	CProposerIsAbstractable(s.proposer)
	// 	&&
	// 	CAcceptorIsAbstractable(s.acceptor)
	// 	&&
	// 	CLearnerIsAbstractable(s.learner)
	// 	&&
	// 	CExecutorIsAbstractable(s.executor)
	// }

	// function AbstractifyCReplicaToLReplica(
	// 	s : CReplica) : LReplica
	// 	// requires CReplicaIsAbstractable(s)
  //   requires CReplicaIsValid(s)
  //   /*
  //   We need
  //     requires CProposerIsValid(s) /* we need SetIsInjective */
  //   */
	// {
	// 	LReplica(
  //     AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), 
  //     s.nextHeartbeatTime, 
  //     AbstractifyCProposerToLProposer(s.proposer), 
  //     AbstractifyCAcceptorToLAcceptor(s.acceptor), 
  //     AbstractifyCLearnerToLLearner(s.learner), 
  //     AbstractifyCExecutorToLExecutor(s.executor))
	// }

  /* ----------------------------------------- */


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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextReadClockMaybeSendHeartbeat(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCClockReadingToClockReading(clock),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
    reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_MaybeEnterPhase2_Postconditions(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
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
    reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeMakeDecision(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica:LReplica, replica':CReplica,
                                                                 packets_sent:OutboundPackets)
    reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeExecute(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  /* ----------------------------------------- */

	// function method CReplicaInit(
	// 	c : CReplicaConstants) : CReplica
	// 	// requires CWellFormedLConfiguration(c.all.config)
	// 	requires CReplicaConstantsIsValid(c)
	// 	ensures var r := CReplicaInit(c); CReplicaIsValid(r) && LReplicaInit(AbstractifyCReplicaToLReplica(r), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	// {
	// 	CReplica(acceptor := CAcceptorInit(c), constants := c, executor := CExecutorInit(c), learner := CLearnerInit(c), nextHeartbeatTime := 0, proposer := CProposerInit(c))
	// }

	// function method {:axiom} CReplicaNextProcessInvalid(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_Invalid?
	// 	ensures var (s', non_empty_sequential_sent_packets) := CReplicaNextProcessInvalid(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(non_empty_sequential_sent_packets) && LReplicaNextProcessInvalid(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(non_empty_sequential_sent_packets))
	// {
	// 	(
	// 		s,
	// 		PacketSequence([])
	// 	)
	// }

	// function method CReplicaNextProcessRequest(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_Request?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Process_Request_Preconditions(s, received_packet)
  //   ensures  
  //     var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet);
  //     Replica_Next_Process_Request_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)
  // {
  //   lemma_CReplicaNextProcessRequest_pre(s, received_packet);

  //   var (s', sequential_sent_packets) := 
	// 	if  && received_packet.src in s.executor.reply_cache && s.executor.reply_cache[received_packet.src].CReply? && received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno
	// 	then 
	// 		(
	// 			s,
	// 			CExecutorProcessRequest(s.executor, received_packet)
	// 		)
	// 	else 
	// 		(
	// 			s.(
	// 				proposer := CProposerProcessRequest(s.proposer, received_packet)
	// 			),
	// 			OutboundPacket(None())
	// 		)
  //   ;

  //   lemma_CReplicaNextProcessRequest(s, received_packet, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextProcess1a(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_1a?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcess1a(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Process_1a_Preconditions(s, received_packet)
  //   ensures var (s', sequential_sent_packets) := CReplicaNextProcess1a(s, received_packet);
  //     Replica_Next_Process_1a_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)
  // {
  //   lemma_CReplicaNextProcess1a_pre(s, received_packet);

	// 	var (t0, t1) := CAcceptorProcess1a(s.acceptor, received_packet); 

  //   var (s', sequential_sent_packets) :=
	// 	(
	// 		s.(
	// 			acceptor := t0
	// 		),
	// 		t1
	// 	)
  //   ;

  //   lemma_CReplicaNextProcess1a(s, received_packet, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextProcess1b(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_1b?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcess1b(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess1b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Process_1b_Preconditions(s, received_packet);
  //   ensures 
  //     var (s', sequential_sent_packets) := CReplicaNextProcess1b(s, received_packet);
  //     Replica_Next_Process_1b_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)
  // {
  //   var (s', sequential_sent_packets) := 
	// 	if  && received_packet.src in s.proposer.constants.all.config.replica_ids && received_packet.msg.bal_1b == s.proposer.max_ballot_i_sent_1a && s.proposer.current_state == 1 && (forall other_packet :: other_packet in s.proposer.received_1b_packets ==> other_packet.src != received_packet.src)
	// 	then 
	// 		(
	// 			s.(
	// 				proposer := CProposerProcess1b(s.proposer, received_packet),
	// 				acceptor := CAcceptorTruncateLog(s.acceptor, received_packet.msg.log_truncation_point)
	// 			),
	// 			OutboundPacket(None())
	// 		)
	// 	else 
	// 		(
	// 			s,
	// 			OutboundPacket(None())
	// 		)
  //   ;
  //   lemma_CReplicaNextProcess1b(s, received_packet, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextProcessStartingPhase2(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_StartingPhase2?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcessStartingPhase2(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessStartingPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Process_StartingPhase2_Preconditions(s, received_packet)
  //   ensures 
  //     var (s', sequential_sent_packets) := CReplicaNextProcessStartingPhase2(s, received_packet);
  //     Replica_Next_Process_StartingPhase2_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)
  // {
	// 	var (t0, t1) := CExecutorProcessStartingPhase2(s.executor, received_packet); 
		
  //   var (s', sequential_sent_packets) :=
  //   (
	// 		s.(
	// 			executor := t0
	// 		),
	// 		t1
	// 	)
  //   ;
  //   lemma_CReplicaNextProcessStartingPhase2(s, received_packet, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextProcess2a(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_2a?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcess2a(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Process_2a_Preconditions(s, received_packet)
  //   ensures  
  //     var (s', sequential_sent_packets) := CReplicaNextProcess2a(s, received_packet);
  //     Replica_Next_Process_2a_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)

  // {
	// 	var m := received_packet.msg; 

  //   var (s', sequential_sent_packets) := 
	// 	if  && received_packet.src in s.acceptor.constants.all.config.replica_ids && CBalLeq(s.acceptor.max_bal, m.bal_2a) && CLeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val)
	// 	then 
	// 		var (t0, t1) := CAcceptorProcess2a(s.acceptor, received_packet); 
	// 		(
	// 			s.(
	// 				acceptor := t0
	// 			),
	// 			t1
	// 		)
	// 	else 
	// 		(
	// 			s,
	// 			OutboundPacket(None())
	// 		)
  //   ;

  //   lemma_CReplicaNextProcess2a(s, received_packet, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
  // }

	// function method CReplicaNextProcess2b(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_2b?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcess2b(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Process_2b_Preconditions(s, received_packet)
  //   ensures
  //     var (s', sequential_sent_packets) := CReplicaNextProcess2b(s, received_packet); 
  //     Replica_Next_Process_2b_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)

  // {
  //   lemma_CReplicaNextProcess2b_pre(s, received_packet);

	// 	var opn := received_packet.msg.opn_2b; 
	// 	var op_learnable := s.executor.ops_complete < opn || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.COutstandingOpUnknown?); 
		
  //   var (s', sequential_sent_packets) := 
  //   if op_learnable
	// 	then 
	// 		(
	// 			s.(
	// 				learner := CLearnerProcess2b(s.learner, received_packet)
	// 			),
	// 			OutboundPacket(None())
	// 		)
	// 	else 
	// 		(
	// 			s,
	// 			OutboundPacket(None())
	// 		)
  //   ;

  //   lemma_CReplicaNextProcess2b(s, received_packet, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextProcessReply(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_Reply?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcessReply(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessReply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	// {
	// 	(
	// 		s,
	// 		OutboundPacket(None())
	// 	)
	// }

	// function method CReplicaNextProcessAppStateSupply(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_AppStateSupply?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateSupply(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessAppStateSupply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Process_AppStateSupply_Preconditions(s, received_packet)
  //   ensures  
  //     var (s', sequential_sent_packets) := CReplicaNextProcessAppStateSupply(s, received_packet);
  //     Replica_Next_Process_AppStateSupply_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s',
  //        received_packet, sequential_sent_packets)
  // {
  //   var (s', sequential_sent_packets) :=
	// 	if received_packet.src in s.executor.constants.all.config.replica_ids && received_packet.msg.opn_state_supply > s.executor.ops_complete
	// 	then 
	// 		(
	// 			s.(
	// 				learner := CLearnerForgetOperationsBefore(s.learner, received_packet.msg.opn_state_supply),
	// 				executor := CExecutorProcessAppStateSupply(s.executor, received_packet)
	// 			),
	// 			OutboundPacket(None())
	// 		)
	// 	else 
	// 		(
	// 			s,
	// 			OutboundPacket(None())
	// 		)
  //   ;
  //   lemma_CReplicaNextProcessAppStateSupply(s, received_packet, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextProcessAppStateRequest(
	// 	s : CReplica ,
	// 	received_packet : CPacket) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_AppStateRequest?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateRequest(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessAppStateRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Process_AppStateRequest_Preconditions(s, received_packet)
  //   ensures  
  //   var (s', sequential_sent_packets) := CReplicaNextProcessAppStateRequest(s, received_packet);
  //   Replica_Next_Process_AppStateRequest_Postconditions(
  //     (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)
  // {
  //   var (s', sequential_sent_packets) :=
	// 	var (t0, t1_1) := CExecutorProcessAppStateRequest(s.executor, received_packet); 
	// 	(
	// 		s.(
	// 			executor := t0
	// 		),
	// 		t1_1
	// 	)
  //   ;
  //   lemma_CReplicaNextProcessAppStateRequest(s, received_packet, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextProcessHeartbeat(
	// 	s : CReplica ,
	// 	received_packet : CPacket ,
	// 	clock : int) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	requires CPacketIsValid(received_packet)
	// 	requires received_packet.msg.CMessage_Heartbeat?
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextProcessHeartbeat(s, received_packet, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), clock, AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
    
  // {
  //   lemma_CReplicaNextProcessHeartbeat_Pre(s, received_packet);

  //   var (s', sequential_sent_packets) := 
	// 	(
	// 		s.(
	// 			proposer := CProposerProcessHeartbeat(s.proposer, received_packet, clock),
	// 			acceptor := CAcceptorProcessHeartbeat(s.acceptor, received_packet)
	// 		),
	// 		OutboundPacket(None())
	// 	)
  //   ;
  //   lemma_CReplicaNextProcessHeartbeat(s, received_packet, clock, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
	// 	s : CReplica) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(s)
  //   ensures 
  //     var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s);
  //     Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', sequential_sent_packets)
  // {
	// 	var (t0, t1_0) := CProposerMaybeEnterNewViewAndSend1a(s.proposer); 
  //   var (s', sequential_sent_packets) := 
	// 	(
	// 		s.(
	// 			proposer := t0
	// 		),
	// 		t1_0
	// 	)
  //   ;
  //   lemma_CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextSpontaneousMaybeEnterPhase2(
	// 	s : CReplica) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterPhase2(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeEnterPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_MaybeEnterPhase2_Preconditions(s)
  //   ensures 
  //     var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterPhase2(s); 
  //     Replica_Next_MaybeEnterPhase2_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', sequential_sent_packets)
  // {
	// 	var (t0, t1_0) := CProposerMaybeEnterPhase2(s.proposer, s.acceptor.log_truncation_point); 
  //   var (s', sequential_sent_packets) := 
  //   (
	// 		s.(
	// 			proposer := t0
	// 		),
	// 		t1_0
	// 	)
  //   ;
  //   lemma_CReplicaNextSpontaneousMaybeEnterPhase2(s, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

  // /* 没有更换是因为调用的method还没有被修改成function method */
  // method CReplicaNextReadClockMaybeNominateValueAndSend2a(replica:CReplica, clock:CClockReading) returns (replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica)
  //   ensures Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions((AbstractifyCReplicaToLReplica(replica)),
  //                                                                             replica', clock, packets_sent)
  // {
  //   var newProposer, packets := CProposerMaybeNominateValueAndSend2a(replica.proposer, clock.t, replica.acceptor.log_truncation_point);
  //   replica' := replica.(proposer := newProposer);
  //   packets_sent := packets;

  //   lemma_CReplicaNextReadClockMaybeNominateValueAndSend2a(replica, clock, replica', packets_sent);
  // }

  // method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
  //   requires CReplicaIsValid(s)
  //   ensures CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) 
  //   ensures LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  //   ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions((AbstractifyCReplicaToLReplica(s)),
  //                                                                                  s', sequential_sent_packets)
  // {
  //   ghost var ss := AbstractifyCReplicaToLReplica(s);
  //   var n := CMinQuorumSize(s.constants.all.config);
  //   assert n <= |s.constants.all.config.replica_ids|;
  //   assert |s.acceptor.constants.all.config.replica_ids| == |s.acceptor.last_checkpointed_operation|;
  //   assert s.constants == s.acceptor.constants;
  //   assert |s.constants.all.config.replica_ids| == |s.acceptor.last_checkpointed_operation|;
  //   var opn := ComputeNthHighestValueSeq(s.acceptor.last_checkpointed_operation, n);
  //   // assert CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) == 
  //   //         IsLogTruncationPointValid(
  //   //       opn as int,
  //   //       AbstractifySeq(s.acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber),
  //   //       AbstractifyCConfigurationToLConfiguration(s.constants.all.config)
  //   //     );

  //   assert IsLogTruncationPointValid(
  //         AbstractifyCOperationNumberToOperationNumber(opn),
  //         AbstractifySeq(s.acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber),
  //         AbstractifyCConfigurationToLConfiguration(s.constants.all.config)
  //       );
  //   assert AbstractifyCOperationNumberToOperationNumber(opn) == opn as int;
  //   assert AbstractifySeq(s.acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber) == ss.acceptor.last_checkpointed_operation;
  //   assert AbstractifyCConfigurationToLConfiguration(s.constants.all.config) == ss.constants.all.config;
  //   assert IsLogTruncationPointValid(opn as int, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);

  //   if opn > s.acceptor.log_truncation_point { 
  //       // ghost var op :| op in ss.acceptor.last_checkpointed_operation && IsLogTruncationPointValid(op, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);
  //       var newAcceptor := CAcceptorTruncateLog(s.acceptor, opn);
  //       s' := s.(acceptor := newAcceptor);
  //       sequential_sent_packets := Broadcast(CBroadcastNop);

  //       // assert opn as int == op;
  //       // ghost var opp := opn as int;
  //       // assert opp in ss.acceptor.last_checkpointed_operation;
  //       // assert IsLogTruncationPointValid(opp, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);
  //       // assert opp in ss.acceptor.last_checkpointed_operation && IsLogTruncationPointValid(opp, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);
  //       // assert CReplicaIsValid(s');
  //       // assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
  //       //     AbstractifyCReplicaToLReplica(s),
  //       //     AbstractifyCReplicaToLReplica(s'),
  //       //     AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
  //   }
  //   else {
  //       s' := s;
  //       sequential_sent_packets := Broadcast(CBroadcastNop);
  //   }
  //   lamme_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
  // }

	// function method CReplicaNextSpontaneousMaybeMakeDecision(
	// 	s : CReplica) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeMakeDecision(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeMakeDecision(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(s)
  //   ensures
  //     var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeMakeDecision(s);
  //     Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', sequential_sent_packets)
  // {
	// 	var opn := s.executor.ops_complete; 
		
  //   var (s', sequential_sent_packets) :=
  //   if  && s.executor.next_op_to_execute.COutstandingOpUnknown? && opn in s.learner.unexecuted_learner_state && |s.learner.unexecuted_learner_state[opn].received_2b_message_senders| >= CMinQuorumSize(s.learner.constants.all.config)
	// 	then 
	// 		(
	// 			s.(
	// 				executor := CExecutorGetDecision(s.executor, s.learner.max_ballot_seen, opn, s.learner.unexecuted_learner_state[opn].candidate_learned_value)
	// 			),
	// 			OutboundPacket(None())
	// 		)
	// 	else 
	// 		(
	// 			s,
	// 			OutboundPacket(None())
	// 		)
  //   ;

  //   lemma_CReplicaNextSpontaneousMaybeMakeDecision(s, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextSpontaneousMaybeExecute(
	// 	s : CReplica) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(s)
  //   ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); 
  //   Replica_Next_Spontaneous_MaybeExecute_Postconditions(
  //     (AbstractifyCReplicaToLReplica(s)), s', sequential_sent_packets)
  // {
  //   var (s', sequential_sent_packets) := 
	// 	if  && s.executor.next_op_to_execute.COutstandingOpKnown? && CLtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) /* && CReplicaConstantsValid(s.executor.constants) */
	// 	then 
	// 		var v := s.executor.next_op_to_execute.v; 
	// 		var (t0, t1_1) := CExecutorExecute(s.executor); 
	// 		(
	// 			s.(
	// 				proposer := CProposerResetViewTimerDueToExecution(s.proposer, v),
	// 				learner := CLearnerForgetDecision(s.learner, s.executor.ops_complete),
	// 				executor := t0
	// 			),
	// 			t1_1
	// 		)
	// 	else 
	// 		(
	// 			s,
	// 			OutboundPacket(None())
	// 		)
  //   ;
  //   lemma_CReplicaNextSpontaneousMaybeExecute(s, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextReadClockMaybeSendHeartbeat(
	// 	s : CReplica ,
	// 	clock : CClockReading) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	// requires CClockReadingIsValid(clock)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextReadClockMaybeSendHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))

  //   requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(s)
  //   ensures
  //     var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock);
  //     Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', clock, sequential_sent_packets)
  // {
  //   var (s', sequential_sent_packets) := 
	// 	if clock.t < s.nextHeartbeatTime
	// 	then 
	// 		(
	// 			s,
	// 			OutboundPacket(None())
	// 		)
	// 	else 
	// 		(
	// 			s.(
	// 				nextHeartbeatTime := UpperBoundedAdditionImpl(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val)
	// 			),
	// 			// BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete))
  //       /* 之后要改 */
  //       Broadcast(
  //         BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete))
  //       )
  //     )
  //   ;
  //   lemma_CReplicaNextReadClockMaybeSendHeartbeat(s, clock, s', sequential_sent_packets);
  //   (s', sequential_sent_packets) 
	// }

	// function method CReplicaNextReadClockCheckForViewTimeout(
	// 	s : CReplica ,
	// 	clock : CClockReading) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	// requires CClockReadingIsValid(clock)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForViewTimeout(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextReadClockCheckForViewTimeout(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(s)
  //   ensures
  //     var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForViewTimeout(s, clock); 
  //    Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(
  //     (AbstractifyCReplicaToLReplica(s)), s', clock, sequential_sent_packets) 
  // {
  //   var (s', sequential_sent_packets) := 
	// 	(
	// 		s.(
	// 			proposer := CProposerCheckForViewTimeout(s.proposer, clock.t)
	// 		),
	// 		OutboundPacket(None())
	// 	)
  //   ;
  //   lemma_CReplicaNextReadClockCheckForViewTimeout(s, clock, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

	// function method CReplicaNextReadClockCheckForQuorumOfViewSuspicions(
	// 	s : CReplica ,
	// 	clock : CClockReading) : (CReplica, OutboundPackets)
	// 	requires CReplicaIsValid(s)
	// 	// requires CClockReadingIsValid(clock)
	// 	ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
  //   requires Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(s)
  //   ensures
  //     var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, clock);
  //     Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(
  //       (AbstractifyCReplicaToLReplica(s)), s', clock, sequential_sent_packets)
                                                                                
  // {
  //   var (s', sequential_sent_packets) :=
	// 	(
	// 		s.(
	// 			proposer := CProposerCheckForQuorumOfViewSuspicions(s.proposer, clock.t)
	// 		),
	// 		OutboundPacket(None())
	// 	)
  //   ;
  //   lemma_CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, clock, s', sequential_sent_packets);
  //   (s', sequential_sent_packets)
	// }

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

// method ComputeNthHighestValueSeq(cm:seq<COperationNumber>, n:int) returns (opn:COperationNumber)
//   // requires CLastCheckpointedMapIsAbstractable(cm)
//   requires SeqIsAbstractable(cm,AbstractifyCOperationNumberToOperationNumber)
//   requires 0 < n <= |cm|
//   // requires |cm| < 0xffff_ffff_ffff_ffff
//   ensures  IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySeq(cm, AbstractifyCOperationNumberToOperationNumber), n as int)
// {
//   var a := InsertSort(cm);
//   assert multiset(a[..]) == multiset(cm);
//   assert |a| == |cm|;
//   ghost var s := a[..]; 
//   opn := a[|a|-(n as int)];
//   assert opn == s[|s|-(n as int)];

//   lemma_SortedSequenceMatchCount(s, n as int);
//   assert IsNthHighestValueInSequence(opn, s, n);
//   lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, s, multiset(cm), n);
//   lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, cm, multiset(cm), n);
//   lemma_AbstractionOfCOperationNumberIsNthHighestValueInSequence(opn, cm, n);
// }


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

  // lemma {:axiom} lemma_CReplicaNextProcessRequest_pre(replica:CReplica, inp:CPacket)
  //   requires Replica_Next_Process_Request_Preconditions(replica, inp)
  //   ensures  inp.src in replica.proposer.constants.all.config.replica_ids

  // lemma {:axiom} lemma_CReplicaNextProcessRequest(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_Process_Request_Preconditions(replica, inp)
  //   ensures  Replica_Next_Process_Request_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
  //                                                        inp, packets_sent)

  // lemma {:axiom} lemma_CReplicaNextProcess1a_pre(replica:CReplica, inp:CPacket)
  //   requires Replica_Next_Process_1a_Preconditions(replica, inp)
  //   ensures CBallotIsValid(inp.msg.bal_1a)

  // lemma {:axiom} lemma_CReplicaNextProcess1a(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_Process_1a_Preconditions(replica, inp)
  //   ensures Replica_Next_Process_1a_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  // lemma {:axiom} lemma_CReplicaNextProcess1b(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_Process_1b_Preconditions(replica, inp)
  //   ensures  Replica_Next_Process_1b_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  // lemma {:axiom} lemma_CReplicaNextProcessStartingPhase2(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_Process_StartingPhase2_Preconditions(replica, inp)
  //   ensures Replica_Next_Process_StartingPhase2_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  // lemma {:axiom} lemma_CReplicaNextProcess2a(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_Process_2a_Preconditions(replica, inp)
  //   ensures  Replica_Next_Process_2a_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  // lemma {:axiom} lemma_CReplicaNextProcess2b_pre(replica:CReplica, inp:CPacket)
  //   requires Replica_Next_Process_2b_Preconditions(replica, inp)
  //   ensures CBallotIsValid(inp.msg.bal_2b)

  // lemma {:axiom} lemma_CReplicaNextProcess2b(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_Process_2b_Preconditions(replica, inp)
  //   ensures Replica_Next_Process_2b_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  // lemma {:axiom} lemma_CReplicaNextProcessAppStateSupply(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_Process_AppStateSupply_Preconditions(replica, inp)
  //   ensures  Replica_Next_Process_AppStateSupply_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
  //                                                               inp, packets_sent)

  // lemma {:axiom} lemma_CReplicaNextProcessAppStateRequest(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
  //   requires Replica_Next_Process_AppStateRequest_Preconditions(replica, inp)
  //   ensures  Replica_Next_Process_AppStateRequest_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
  //                                                                inp, packets_sent)

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



// datatype ReplicaState = ReplicaState(
//   constants:CReplicaConstants,
//   nextHeartbeatTime:uint64,
//   proposer:ProposerState,
//   acceptor:AcceptorState,
//   learner:CLearnerState,
//   executor:ExecutorState
//   )

// predicate CReplicaStateValid(replica:ReplicaState)
// {
//     && ReplicaStateIsAbstractable(replica)
//   && CReplicaConstansValid(replica.constants)
//   && CProposerStateValid(replica.proposer)
//   && AcceptorIsValid(replica.acceptor)
//   && CLearnerStateVaild(replica.learner)
//   && ExecutorStateValid(replica.executor)
// }

// predicate ReplicaStateIsAbstractable(replica:ReplicaState)
// {
//   && ReplicaConstantsStateIsAbstractable(replica.constants)
//   && ProposerIsAbstractable(replica.proposer)
//   && AcceptorIsAbstractable(replica.acceptor)
//   && LearnerState_IsAbstractable(replica.learner)
//   && ExecutorState_IsAbstractable(replica.executor)
// }

// function AbstractifyReplicaStateToLReplica(replica:ReplicaState) : (lreplica:LReplica)
//   reads    replica.executor.app.app
//   requires ReplicaStateIsAbstractable(replica)
//   ensures  lreplica.constants == AbstractifyReplicaConstantsStateToLReplicaConstants(replica.constants)
// {
//   LReplica(
//     AbstractifyReplicaConstantsStateToLReplicaConstants(replica.constants),
//     replica.nextHeartbeatTime as int,
//     AbstractifyProposerStateToLProposer(replica.proposer),
//     AbstractifyAcceptorStateToAcceptor(replica.acceptor),
//     AbstractifyLearnerStateToLLearner(replica.learner),
//     AbstractifyExecutorStateToLExecutor(replica.executor))
// }

// predicate ConstantsStayConstant_Replica(replica:LReplica, replica':ReplicaState)
//   requires ReplicaConstantsStateIsAbstractable(replica'.constants)
// {
//   && AbstractifyReplicaConstantsStateToLReplicaConstants(replica'.constants) == replica.constants
//   && replica.constants == replica.proposer.constants
//   && replica.constants == replica.acceptor.constants
//   && replica.constants == replica.learner.constants
//   && replica.constants == replica.executor.constants
//   && replica'.constants == replica'.proposer.constants
//   && replica'.constants == replica'.acceptor.constants
//   && replica'.constants == replica'.learner.rcs
//   && replica'.constants == replica'.executor.constants
// }

// /********* pre conditions *******************/
// predicate Replica_Common_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && CReplicaStateValid(replica)
//   && CPacketIsSendable(inp)
//   && PaxosEndPointIsValid(inp.src, replica.constants.all.config)
// }

// predicate Replica_Next_Process_Heartbeat_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && Replica_Common_Preconditions(replica, inp)
//   && NextAcceptorState_ProcessHeartbeatPreconditions(replica.acceptor, inp.msg, inp.src)
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_Heartbeat?
// }

// predicate Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica:ReplicaState)
// {
//   CReplicaStateValid(replica)
// }

// predicate Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica:ReplicaState)
// {
//   CReplicaStateValid(replica)
// }

// predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica:ReplicaState)
// {
//   CReplicaStateValid(replica)
// }

// predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica:ReplicaState)
// {
//   CReplicaStateValid(replica)
// }

// predicate Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica:ReplicaState)
// {
//   CReplicaStateValid(replica)
// }

// predicate Replica_Next_MaybeEnterPhase2_Preconditions(replica:ReplicaState)
// {
//   CReplicaStateValid(replica)
// }

// predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica:ReplicaState)
// {
//   CReplicaStateValid(replica)
// }

// predicate Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica:ReplicaState)
// {
//   CReplicaStateValid(replica)
// }

// predicate Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica:ReplicaState)
// {
//   CReplicaStateValid(replica)
// }

// predicate Replica_Next_Process_Request_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && Replica_Common_Preconditions(replica, inp)
//   && CProposerStateValid(replica.proposer)
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_Request?
// }

// predicate Replica_Next_Process_1a_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && Replica_Common_Preconditions(replica, inp)
//   && NextAcceptorState_Phase1Preconditions(replica.acceptor, inp.msg, inp.src)
// }

// predicate Replica_Next_Process_1b_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && Replica_Common_Preconditions(replica, inp)
//   && CProposerStateValid(replica.proposer)
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_1b?
// }

// predicate Replica_Next_Process_StartingPhase2_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && Replica_Common_Preconditions(replica, inp)
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_StartingPhase2?
// }

// predicate Replica_Next_Process_2a_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && Replica_Common_Preconditions(replica, inp)
//   && NextAcceptorState_Phase2Preconditions_AlwaysEnabled(replica.acceptor, inp.msg, inp.src)
// }

// predicate Replica_Next_Process_2b_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && Replica_Common_Preconditions(replica, inp)
//   && LearnerState_Process2b__Preconditions(replica.learner, replica.executor, inp)
// }

// predicate Replica_Next_Process_AppStateRequest_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && Replica_Common_Preconditions(replica, inp)
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_AppStateRequest?
// }

// predicate Replica_Next_Process_AppStateSupply_Preconditions(replica:ReplicaState, inp:CPacket)
// {
//   && Replica_Common_Preconditions(replica, inp)
//   && inp.msg.CMessage_AppStateSupply?
//   && LearnerState_ForgetOperationsBefore__Preconditions(replica.learner, inp.msg.opn_state_supply)
// }
// /************** post conditions *********************/
// predicate Replica_Common_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket, packets_sent:OutboundPackets)
// {
//   && CReplicaConstansValid(replica'.constants)
//   && CPacketIsSendable(inp)
//   && PaxosEndPointIsValid(inp.src, replica'.constants.all.config)
//   && ReplicaStateIsAbstractable(replica')
//   && ConstantsStayConstant_Replica(replica, replica')
//   && CReplicaStateValid(replica')
//   && OutboundPacketsIsValid(packets_sent)
//   && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
//   && OutboundPacketsIsAbstractable(packets_sent)
// }


// predicate Replica_Next_Process_AppStateSupply_Postconditions(replica:LReplica, replica':ReplicaState,
//                                                              inp:CPacket, packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_AppStateSupply?
//   && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
//   && LReplicaNextProcessAppStateSupply(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCPacketToRslPacket(inp),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Process_AppStateRequest_Postconditions(replica:LReplica, replica':ReplicaState,
//                                                               inp:CPacket, packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_AppStateRequest?
//   && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
//   && LReplicaNextProcessAppStateRequest(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCPacketToRslPacket(inp),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Process_2b_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
//                                                  packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_2b?
//   && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
//   && LReplicaNextProcess2b(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCPacketToRslPacket(inp),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Process_2a_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
//                                                  packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_2a?
//   && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
//   && LReplicaNextProcess2a(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCPacketToRslPacket(inp),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Process_StartingPhase2_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
//                                                              packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_StartingPhase2?
//   && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
//   && LReplicaNextProcessStartingPhase2(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCPacketToRslPacket(inp),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Process_1b_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
//                                                  packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_1b?
//   && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
//   && LReplicaNextProcess1b(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCPacketToRslPacket(inp),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Process_1a_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
//                                                  packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_1a?
//   && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
//   && LReplicaNextProcess1a(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCPacketToRslPacket(inp),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Process_Request_Postconditions(replica:LReplica, replica':ReplicaState, inp:CPacket,
//                                                       packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   // run-time error
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_Request?
//   && Replica_Common_Postconditions(replica, replica', inp, packets_sent)

//   // refinement
//   && LReplicaNextProcessRequest(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCPacketToRslPacket(inp),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate ReplicaCommonPostconditions(replica:LReplica, replica':ReplicaState, sent_packets:OutboundPackets)
// {
//     && CReplicaConstansValid(replica'.constants)
//     && AbstractifyReplicaConstantsStateToLReplicaConstants(replica'.constants) == replica.constants
//     && ReplicaStateIsAbstractable(replica')
//     && CReplicaStateValid(replica')
//     && OutboundPacketsIsValid(sent_packets)
//     && OutboundPacketsIsAbstractable(sent_packets)
//     && OutboundPacketsHasCorrectSrc(sent_packets, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
// }


// predicate Replica_Next_Process_Heartbeat_Postconditions(replica:LReplica, replica':ReplicaState,
//                                                         inp:CPacket, clock:uint64, packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && CPacketIsAbstractable(inp)
//   && inp.msg.CMessage_Heartbeat?
//   && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
//   && LReplicaNextProcessHeartbeat(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCPacketToRslPacket(inp),
//       clock as int,
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }


// predicate Replica_Common_Postconditions_NoPacket(replica:LReplica, replica':ReplicaState, packets_sent:OutboundPackets)
// {
//   && CReplicaConstansValid(replica'.constants)
//   && ReplicaStateIsAbstractable(replica')
//   && ConstantsStayConstant_Replica(replica, replica')
//   && CReplicaStateValid(replica')
//   && OutboundPacketsIsValid(packets_sent)
//   && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
//   && OutboundPacketsIsAbstractable(packets_sent)
// }

// predicate Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(
//   replica:LReplica,
//   replica':ReplicaState,
//   clock:CClockReading,
//   packets_sent:OutboundPackets
//   )
//   reads replica'.executor.app.app
// {
//   && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
//   && LReplicaNextReadClockMaybeNominateValueAndSend2a(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCClockReadingToClockReading(clock),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(
//   replica:LReplica,
//   replica':ReplicaState,
//   clock:CClockReading,
//   packets_sent:OutboundPackets
//   )
//   reads replica'.executor.app.app
// {
//   && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
//   && LReplicaNextReadClockCheckForViewTimeout(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCClockReadingToClockReading(clock),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(
//   replica:LReplica,
//   replica':ReplicaState,
//   clock:CClockReading,
//   packets_sent:OutboundPackets
//   )
//   reads replica'.executor.app.app
// {
//   && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
//   && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCClockReadingToClockReading(clock),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(
//   replica:LReplica,
//   replica':ReplicaState,
//   clock:CClockReading,
//   packets_sent:OutboundPackets
//   )
//   reads replica'.executor.app.app
// {
//   && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
//   && LReplicaNextReadClockMaybeSendHeartbeat(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyCClockReadingToClockReading(clock),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica:LReplica, replica':ReplicaState, packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
//   && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_MaybeEnterPhase2_Postconditions(replica:LReplica, replica':ReplicaState, packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
//   && LReplicaNextSpontaneousMaybeEnterPhase2(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(
//   replica:LReplica,
//   replica':ReplicaState,
//   packets_sent:OutboundPackets
//   )
//   reads replica'.executor.app.app
// {
//   && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
//   && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(
//   replica:LReplica,
//   replica':ReplicaState,
//   packets_sent:OutboundPackets
//   )
//   reads replica'.executor.app.app
// {
//   && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
//   && LReplicaNextSpontaneousMaybeMakeDecision(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }

// predicate Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica:LReplica, replica':ReplicaState,
//                                                                packets_sent:OutboundPackets)
//   reads replica'.executor.app.app
// {
//   && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
//   && LReplicaNextSpontaneousMaybeExecute(
//       replica,
//       AbstractifyReplicaStateToLReplica(replica'),
//       AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
// }


// method CReplicaInit(constants:CReplicaConstants) returns (replica:ReplicaState)
// requires CReplicaConstansValid(constants)
//   ensures CReplicaStateValid(replica)
//   ensures replica.constants == constants
//   ensures LReplicaInit(AbstractifyReplicaStateToLReplica(replica), AbstractifyReplicaConstantsStateToLReplicaConstants(constants))
//   // ensures MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
//   // ensures MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
//   // ensures fresh(cur_req_set) && fresh(prev_req_set) && cur_req_set != prev_req_set
//   // ensures fresh(reply_cache_mutable)
//   // ensures replica.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
// {
//     var proposer := CProposerInit(constants);
//     var acceptor := CAcceptorInit(constants);
//     var learner := CLearnerInit(constants);
//     var executor := CExecutorInit(constants);
//     replica := ReplicaState(
//         constants,
//         0,
//         proposer,
//         acceptor,
//         learner,
//         executor
//     );
// }

// method {:axiom} CReplicaNextProcessInvalid(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
// {
//     replica' := replica;
//     packets_sent := PacketSequence([]);
// }

// method CReplicaNextProcessRequest(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Process_Request_Preconditions(replica, inp)
//     ensures  Replica_Next_Process_Request_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                        inp, packets_sent)
// {
//     var start_time := Time.GetDebugTimeTicks();
//     if |inp.msg.val| > MaxAppRequestSize(){
//         replica' := replica;
//         packets_sent := PacketSequence([]);
//     } else {
//         if inp.src in replica.executor.reply_cache && replica.executor.reply_cache[inp.src].CReply? && inp.msg.seqno <= replica.executor.reply_cache[inp.src].seqno {
//             packets_sent := CExecutorProcessRequest(replica.executor, inp);
//             replica' := replica;
//         } else {
//             var newProposer := CProposerProcessRequest(replica.proposer, inp);
//             replica' := replica.(proposer := newProposer);
//             packets_sent := Broadcast(CBroadcastNop);
//         }
//     }

//     lemma_CReplicaNextProcessRequest(replica, inp, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextProcessRequest(replica:ReplicaState, inp:CPacket, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Process_Request_Preconditions(replica, inp)
//     ensures  Replica_Next_Process_Request_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                        inp, packets_sent)

// method CReplicaNextProcess1a(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Process_1a_Preconditions(replica, inp)
//     ensures Replica_Next_Process_1a_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)
// {
//   var start_time := Time.GetDebugTimeTicks();
//     var newAcceptor, packets := CAcceptorProcess1a(replica.acceptor, inp);
//     replica' := replica.(acceptor := newAcceptor);
//     packets_sent := Broadcast(packets);

//     lemma_CReplicaNextProcess1a(replica, inp, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextProcess1a(replica:ReplicaState, inp:CPacket, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Process_1a_Preconditions(replica, inp)
//     ensures Replica_Next_Process_1a_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)

// method CReplicaNextProcess1b(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Process_1b_Preconditions(replica, inp)
//     ensures  Replica_Next_Process_1b_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)
// {
//     var start_time := Time.GetDebugTimeTicks();

//     if inp.src in replica.proposer.constants.all.config.replica_ids 
//         && inp.msg.bal_1b == replica.proposer.max_ballot_i_sent_1a
//         && replica.proposer.current_state == 1 
//         && forall other_packet :: other_packet in replica.proposer.received_1b_packets ==> other_packet.src != inp.src
//     {
//         var newProposer := CProposerProcess1b(replica.proposer, inp);
//         var newAcceptor:= CAcceptorTruncateLog(replica.acceptor, inp.msg.log_truncation_point);
//         replica' := replica.(proposer := newProposer,
//                             acceptor := newAcceptor);
//         packets_sent := Broadcast(CBroadcastNop);
//     } else {
//         replica' := replica;
//         packets_sent := Broadcast(CBroadcastNop);
//     }

//     lemma_CReplicaNextProcess1b(replica, inp, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextProcess1b(replica:ReplicaState, inp:CPacket, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Process_1b_Preconditions(replica, inp)
//     ensures  Replica_Next_Process_1b_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)

// method CReplicaNextProcessStartingPhase2(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_StartingPhase2_Preconditions(replica, inp)
//   ensures Replica_Next_Process_StartingPhase2_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)
// {
//   // if inp.src in replica.constants.all.config.replica_ids
//   // {
//   //   var index := CGetReplicaIndex(inp.src, replica.constants.all.config);
//   // print ("ReplicaImpl: Received a start phase 2 message from", index, "\n");
//   // } else {
//   //   print("start phase 2 wrong\n");
//   // }
//     var start_time := Time.GetDebugTimeTicks();

//     var newExecutor, packets := CExecutorProcessStartingPhase2(replica.executor, inp);
//     replica' := replica.(executor := newExecutor);
//     packets_sent := Broadcast(packets);

//     // var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }

//     lemma_CReplicaNextProcessStartingPhase2(replica, inp, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextProcessStartingPhase2(replica:ReplicaState, inp:CPacket, replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_StartingPhase2_Preconditions(replica, inp)
//   ensures Replica_Next_Process_StartingPhase2_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)

// method CReplicaNextProcess2a(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_2a_Preconditions(replica, inp)
//   ensures  Replica_Next_Process_2a_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)
// {
//   //   if inp.src in replica.constants.all.config.replica_ids
//   // {
//   //  var index := CGetReplicaIndex(inp.src, replica.constants.all.config);
//   // print ("ReplicaImpl: Received a 2a message from", index, "\n");
//   // } else {
//   //   print("2a wrong\n");
//   // }
//     var start_time := Time.GetDebugTimeTicks();

//     var m := inp.msg;
//     if  && inp.src in replica.acceptor.constants.all.config.replica_ids 
//         && CBalLeq(replica.acceptor.maxBallot, m.bal_2a) 
//         && CLeqUpperBound(m.opn_2a, replica.acceptor.constants.all.params.max_integer_val)
//     {
//         var newAcceptor, packets := CAcceptorProcess2a(replica.acceptor, inp);
//         replica' := replica.(acceptor := newAcceptor);
//         packets_sent := Broadcast(packets);
//     } else {
//         replica' := replica;
//         packets_sent := Broadcast(CBroadcastNop);
//     }

//     // var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }

//     lemma_CReplicaNextProcess2a(replica, inp, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextProcess2a(replica:ReplicaState, inp:CPacket, replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_2a_Preconditions(replica, inp)
//   ensures  Replica_Next_Process_2a_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)

// method CReplicaNextProcess2b(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_2b_Preconditions(replica, inp)
//   ensures Replica_Next_Process_2b_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)
// {
//   // if inp.src in replica.constants.all.config.replica_ids
//   // {
//   // var index := CGetReplicaIndex(inp.src, replica.constants.all.config);
//   // print ("ReplicaImpl: Received a 2b message from", index, "\n");
//   // } else {
//   //   print("2b wrong\n");
//   // }
//     var start_time := Time.GetDebugTimeTicks();

//     var copn := inp.msg.opn_2b;
//     var cop_learnable := replica.executor.ops_complete < copn || (replica.executor.ops_complete == copn && replica.executor.next_op_to_execute.COutstandingOpUnknown?);
//     if cop_learnable {
//         var newLearner := CLearnerProcess2b(replica.learner, inp);
//         packets_sent := Broadcast(CBroadcastNop);
//         replica' := replica.(learner := newLearner);
//     } else {
//         replica' := replica;
//         packets_sent := Broadcast(CBroadcastNop);
//     }

//     // var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }

//     lemma_CReplicaNextProcess2b(replica, inp, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextProcess2b(replica:ReplicaState, inp:CPacket, replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_2b_Preconditions(replica, inp)
//   ensures Replica_Next_Process_2b_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', inp, packets_sent)

// method CReplicaNextProcessReply(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
// requires CReplicaStateValid(replica)
// requires inp.msg.CMessage_Reply?
// {
//   // print ("ReplicaImpl: Received a Reply message\n");
  
//     packets_sent := Broadcast(CBroadcastNop);
//     replica' := replica;
// }

// method CReplicaNextProcessAppStateSupply(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_AppStateSupply_Preconditions(replica, inp)
//   ensures  Replica_Next_Process_AppStateSupply_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                               inp, packets_sent)
// {
//   var start_time := Time.GetDebugTimeTicks();

//     if (&& inp.src in replica.executor.constants.all.config.replica_ids
//         && inp.msg.opn_state_supply > replica.executor.ops_complete)
//     {
//         var newLearner := CLearnerForgetOperationsBefore(replica.learner, inp.msg.opn_state_supply);
//         var newExecutor := CExecutorProcessAppStateSupply(replica.executor, inp);
//         replica' := replica.(learner := newLearner, executor := newExecutor);
//         packets_sent := Broadcast(CBroadcastNop);
//     } else {
//         replica' := replica;
//         packets_sent := Broadcast(CBroadcastNop);
//     }

//     // var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }
    
//     lemma_CReplicaNextProcessAppStateSupply(replica, inp, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextProcessAppStateSupply(replica:ReplicaState, inp:CPacket, replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_AppStateSupply_Preconditions(replica, inp)
//   ensures  Replica_Next_Process_AppStateSupply_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                               inp, packets_sent)

// method CReplicaNextProcessAppStateRequest(replica:ReplicaState, inp:CPacket) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_AppStateRequest_Preconditions(replica, inp)
//   ensures  Replica_Next_Process_AppStateRequest_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                inp, packets_sent)
// {
//     var newExecutor, packets := CExecutorProcessAppStateRequest(replica.executor, inp);
//     replica' := replica.(executor := newExecutor);
//     packets_sent := packets;
//     lemma_CReplicaNextProcessAppStateRequest(replica, inp, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextProcessAppStateRequest(replica:ReplicaState, inp:CPacket, replica':ReplicaState, packets_sent:OutboundPackets)
//   requires Replica_Next_Process_AppStateRequest_Preconditions(replica, inp)
//   ensures  Replica_Next_Process_AppStateRequest_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                inp, packets_sent)

// // method {:verify false} CReplicaNextProcessHeartbeat(replica:ReplicaState, inp:CPacket, clock:uint64) returns (replica':ReplicaState, packets_sent:OutboundPackets)
// //     requires CReplicaStateValid(replica)
// //     requires inp.msg.CMessage_Heartbeat?
// //     ensures  Replica_Next_Process_Heartbeat_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
// //                                                                 inp, clock, packets_sent)
// //     ensures  replica'.executor == replica.executor
// // {
// //     var newProposer := CProposerProcessHeartbeat(replica.proposer, inp, clock);
// //     var newAcceptor := CAcceptorProcessHeartbeat(replica.acceptor, inp);
// //     replica' := replica.(proposer := newProposer,
// //                         acceptor := newAcceptor);
// //     packets_sent := Broadcast(CBroadcastNop);
// // }

// method CReplicaNextProcessHeartbeat(replica:ReplicaState, inp:CPacket, clock:uint64) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     requires CReplicaStateValid(replica)
//     requires inp.msg.CMessage_Heartbeat?
//     ensures  Replica_Next_Process_Heartbeat_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                 inp, clock, packets_sent)
//     ensures  replica'.executor == replica.executor
// {
//    // print ("ReplicaImpl: Received a Hearbeat message\n");
//    var start_time := Time.GetDebugTimeTicks();

//     var newProposer := CProposerProcessHeartbeat(replica.proposer, inp, clock);
//     var newAcceptor := CAcceptorProcessHeartbeat(replica.acceptor, inp);
//     replica' := replica.(proposer := newProposer,
//                         acceptor := newAcceptor);
//     packets_sent := Broadcast(CBroadcastNop);

//     var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }

//     lemma_CReplicaNextProcessHeartbeat(replica, inp, clock, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextProcessHeartbeat(replica:ReplicaState, inp:CPacket, clock:uint64, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires CReplicaStateValid(replica)
//     requires inp.msg.CMessage_Heartbeat?
//     ensures Replica_Next_Process_Heartbeat_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                          inp, clock, packets_sent)
//     ensures  replica'.executor == replica.executor



// method CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
// requires Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica)
// ensures Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                  packets_sent)
// {
//   // print ("ReplicaImpl: Start a newview and send 1a\n");
//   var start_time := Time.GetDebugTimeTicks();

//     var newProposer, packets := CProposerMaybeEnterNewViewAndSend1a(replica.proposer);
//     replica' := replica.(proposer := newProposer);
//     packets_sent := Broadcast(packets);

//     var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }

//     lemma_CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(replica, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
// requires Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica)
// ensures Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                  packets_sent)

// method CReplicaNextSpontaneousMaybeEnterPhase2(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_MaybeEnterPhase2_Preconditions(replica)
//     ensures Replica_Next_MaybeEnterPhase2_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', packets_sent)
// {
//   // print("ReplicaImpl: enter phase 2\n");
//     var start_time := Time.GetDebugTimeTicks();

//     var newProposer, packets := CProposerMaybeEnterPhase2(replica.proposer, replica.acceptor.log_truncation_point);
//     replica' := replica.(proposer := newProposer);
//     packets_sent := Broadcast(packets);

//     // var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }
//     lemma_CReplicaNextSpontaneousMaybeEnterPhase2(replica, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeEnterPhase2(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_MaybeEnterPhase2_Preconditions(replica)
//     ensures Replica_Next_MaybeEnterPhase2_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica', packets_sent)

// method CReplicaNextReadClockMaybeNominateValueAndSend2a(replica:ReplicaState, clock:CClockReading) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//  requires Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica)
//   ensures Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)),
//                                                                             replica', clock, packets_sent)
// {
//   // print ("ReplicaImpl: Propose a value and send 2a\n");
//     var newProposer, packets := CProposerMaybeNominateValueAndSend2a(replica.proposer, clock.t, replica.acceptor.log_truncation_point);
//     replica' := replica.(proposer := newProposer);
//     packets_sent := Broadcast(packets);
//     lemma_CReplicaNextReadClockMaybeNominateValueAndSend2a(replica, clock, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextReadClockMaybeNominateValueAndSend2a(replica:ReplicaState, clock:CClockReading, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica)
//     ensures Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)),
//                                                                                 replica', clock, packets_sent)

// method SeqToArray<T(0)>(s:seq<T>) returns (a:array<T>)
//   ensures fresh(a)
//   ensures a.Length == |s|
//   ensures forall i :: 0 <= i < |s| ==> s[i] == a[i]
//   ensures a[..] == s
//   ensures fresh(a)
// {
//   a := new T[|s|];

//   var i := 0;
//   while i < |s|
//     invariant 0 <= i <= |s|
//     invariant forall j :: 0 <= j < i ==> s[j] == a[j]
//   {
//     a[i] := s[i];
//     i := i + 1;
//   }
// }

// method SortSeq(a : array<COperationNumber>)
//     modifies a
//     requires a.Length < 0xFFFFFFFFFFFFFFFF
//     ensures multiset(a[..]) == old(multiset(a[..]))
// {
//     if a.Length as uint64 == 0 { return; }
//     var i:uint64 := 1;
//     while i < a.Length as uint64
//         invariant 0 < i <= a.Length as uint64
//         // invariant NeighborSorted_COperationNumber(a, 0, i)
//         invariant multiset(a[..]) == old(multiset(a[..]))
//     {
//         var j:uint64 := i;
//         while 0 < j && a[j-1] > a[j]
//         invariant 0 <= j <= i
//         // invariant NeighborSorted_COperationNumber(a, 0, j)
//         // invariant NeighborSorted_COperationNumber(a, j, i+1)
//         // invariant 0 < j < i ==> a[j-1] <= a[j+1]
//         invariant multiset(a[..]) == old(multiset(a[..]))
//         {
//         // The proof of correctness uses the totality property here.
//         // It implies that if two elements are not previously in
//         // sorted order, they will be after swapping them.
//             a[j], a[j-1] := a[j-1], a[j];
//             j := j - 1;
//         }
//         i := i + 1;
//     }
// }

// method CGetHighestValueAmongMajority(acceptor:AcceptorState, n:uint64) returns (opn:COperationNumber)
// requires AcceptorIsValid(acceptor)
// // requires |acceptor.last_checkpointed_operation| > n as int
// {
//     var i:int := 1;
//     var a := SeqToArray(acceptor.last_checkpointed_operation);
//     SortSeq(a);
//     if(a.Length > a.Length - (n as int) > 0){
//         opn := a[a.Length - (n as int)];
//     }
// }

// // // 对应protocol 中 LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints
// // // 可以有更高效的实现，ironfleet原代码中利用AcceptorModel_GetNthHighestValueAmongReportedCheckpoints直接找最大的opn，消除了exists
// // method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
// //     requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica)
// //     ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)),
// //                                                                                  replica', packets_sent)
// // {
// //     var a := CMinQuorumSize(replica.constants.all.config);
// //     var b := CGetHighestValueAmongMajority(replica.acceptor, a);
// //     if b > replica.acceptor.log_truncation_point
// //     {
// //         var newAcceptor := CAcceptorTruncateLog(replica.acceptor, b);
// //         replica' := replica.(acceptor := newAcceptor);
// //         packets_sent := Broadcast(CBroadcastNop);
// //     } else {
// //         replica' := replica;
// //         packets_sent := Broadcast(CBroadcastNop);
// //     }
// //     lamme_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica, replica', packets_sent);
// //     // if exists opn :: 
// //     //     && CIsLogTruncationPointValid(opn, replica.acceptor.last_checkpointed_operation, replica.constants.all.config)
// //     //     && opn > replica.acceptor.log_truncation_point
// //     // {
// //     //     var newAcceptor := CAcceptorTruncateLog(replica.acceptor, opn);
// //     //     replica' := replica.(acceptor := newAcceptor);
// //     //     packets_sent := Broadcast(CBroadcastNop);
// //     // } else if exists opn :: 
// //     //     && CIsLogTruncationPointValid(opn, replica.acceptor.last_checkpointed_operation, replica.constants.all.config)
// //     //     && opn <= replica.acceptor.log_truncation_point
// //     // {
// //     //     replica' := replica;
// //     //     packets_sent := Broadcast(CBroadcastNop);
// //     // }
// // }

// method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica)
//     ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)),
//                                                                                  replica', packets_sent)
// {
//     var start_time := Time.GetDebugTimeTicks();

//     var a := CMinQuorumSize(replica.constants.all.config);
//     var b := CGetHighestValueAmongMajority(replica.acceptor, a);
//     if b > replica.acceptor.log_truncation_point
//     {
//         var newAcceptor := CAcceptorTruncateLog(replica.acceptor, b);
//         replica' := replica.(acceptor := newAcceptor);
//         packets_sent := Broadcast(CBroadcastNop);

//         // var end_time := Time.GetDebugTimeTicks();
//         // if(end_time >= start_time){
//         //   print end_time - start_time;
//         //   print "\n";
//         // } else {
//         //   print("Wrong");
//         // }
//     } else {
//         replica' := replica;
//         packets_sent := Broadcast(CBroadcastNop);
//     }
//     lamme_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica, replica', packets_sent);
// }

// lemma {:axiom} lamme_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica)
//     ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)),
//                                                                                  replica', packets_sent)

// method CReplicaNextSpontaneousMaybeMakeDecision(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica)
//     requires var opn := replica.executor.ops_complete;
//             || !replica.executor.next_op_to_execute.COutstandingOpUnknown?
//             || opn !in replica.learner.unexecuted_learner_state
//             || |replica.learner.unexecuted_learner_state[opn].received_2b_message_senders| < LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(replica.learner.rcs.all.config))
//     ensures  Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                         packets_sent)
//     ensures  replica' == replica
// {
//   // print ("ReplicaImpl: Make a decision\n");
//   var start_time := Time.GetDebugTimeTicks();

//     var opn := replica.executor.ops_complete;
//     var a := CMinQuorumSize(replica.learner.rcs.all.config) as int;
//     if (&& replica.executor.next_op_to_execute.COutstandingOpUnknown?
//         && opn in replica.learner.unexecuted_learner_state
//         && (|replica.learner.unexecuted_learner_state[opn].received_2b_message_senders|) >= a)
//     {
//         var newExecutor := CExecutorGetDecision(replica.executor, replica.learner.max_ballot_seen, opn, replica.learner.unexecuted_learner_state[opn].candidate_learned_value);
//         replica' := replica.(executor := newExecutor);
//         packets_sent := Broadcast(CBroadcastNop);

//         // var end_time := Time.GetDebugTimeTicks();
//         // if(end_time >= start_time){
//         //   print end_time - start_time;
//         //   print "\n";
//         // } else {
//         //   print("Wrong");
//         // }
//     } else {
//         replica' := replica;
//         packets_sent := Broadcast(CBroadcastNop);
//     }
//     lemma_CReplicaNextSpontaneousMaybeMakeDecision(replica, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeMakeDecision(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica)
//     requires var opn := replica.executor.ops_complete;
//             || !replica.executor.next_op_to_execute.COutstandingOpUnknown?
//             || opn !in replica.learner.unexecuted_learner_state
//             || |replica.learner.unexecuted_learner_state[opn].received_2b_message_senders| < LMinQuorumSize(AbstractifyCPaxosConfigurationToConfiguration(replica.learner.rcs.all.config))
//     ensures  Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                         packets_sent)
//     ensures  replica' == replica

// // 有的sent_packets == []翻译成了 packets_sent := Broadcast(CBroadcastNop)
// // 还有的sent_packets == []翻译成了 packets_sent := OutboundPacket(None)
// // Broadcast(CBroadcastNop) 和 OutboundPacket(None) 有啥区别，看起来都是发了空包
// method CReplicaNextSpontaneousMaybeExecute(replica:ReplicaState) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     // requires CReplicaStateValid(replica)
//     // requires CReplicaConstansValid(replica.executor.constants)
//     requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica)
//     modifies replica.executor.app.app
//     ensures  Replica_Next_Spontaneous_MaybeExecute_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                 packets_sent)
// {
//   // print ("ReplicaImpl: Execute a request\n");
//   var start_time := Time.GetDebugTimeTicks();

//     if && replica.executor.next_op_to_execute.COutstandingOpKnown?
//         // && LtUpperBound(replica.executor.ops_complete, replica.executor.constants.all.params.max_integer_val)
//     {
//         var val := replica.executor.next_op_to_execute.v;
//         var newProposer := CProposerResetViewTimerDueToExecution(replica.proposer, val);
//         var newLearner := CLearnerForgetDecision(replica.learner, replica.executor.ops_complete);
//         var newExecutor, packets := CExecutorExecute(replica.executor);
//         replica' := replica.(proposer := newProposer,
//                             learner := newLearner,
//                             executor := newExecutor);
//         packets_sent := packets;

//         // var end_time := Time.GetDebugTimeTicks();
//         // if(end_time >= start_time){
//         //   print end_time - start_time;
//         //   print "\n";
//         // } else {
//         //   print("Wrong");
//         // }
//     } else {
//         replica' := replica;
//         packets_sent := OutboundPacket(None);
//     }
//     lemma_CReplicaNextSpontaneousMaybeExecute(replica, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeExecute(replica:ReplicaState, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica)
//     ensures  Replica_Next_Spontaneous_MaybeExecute_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                 packets_sent)

// method CReplicaNextReadClockMaybeSendHeartbeat(replica:ReplicaState, clock:CClockReading) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     // requires CReplicaStateValid(replica)
//     requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica)
//     ensures Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                     clock, packets_sent)
// {
//   var start_time := Time.GetDebugTimeTicks();

//     if clock.t < replica.nextHeartbeatTime {
//         replica' := replica;
//         packets_sent := Broadcast(CBroadcastNop);
//     } else {
//         var a := UpperBoundedAdditionImpl(clock.t, replica.constants.all.params.heartbeat_period, replica.constants.all.params.max_integer_val);
//         replica' := replica.(nextHeartbeatTime := a);
//         var packets := BuildBroadcastToEveryone(replica.constants.all.config, replica.constants.my_index, 
//                         CMessage_Heartbeat(replica.proposer.election_state.current_view, 
//                         replica.constants.my_index in replica.proposer.election_state.current_view_suspectors, 
//                         replica.executor.ops_complete));
//         replica' := replica.(nextHeartbeatTime := replica'.nextHeartbeatTime);
//         packets_sent := Broadcast(packets);

//         // var end_time := Time.GetDebugTimeTicks();
//         // if(end_time >= start_time){
//         //   print end_time - start_time;
//         //   print "\n";
//         // } else {
//         //   print("Wrong");
//         // }
//     }
//     lemma_CReplicaNextReadClockMaybeSendHeartbeat(replica, clock, replica', packets_sent);
// }

// lemma {:axiom} lemma_CReplicaNextReadClockMaybeSendHeartbeat(replica:ReplicaState, clock:CClockReading, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica)
//     ensures Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)), replica',
//                                                                     clock, packets_sent)

// method CReplicaNextReadClockCheckForViewTimeout(replica:ReplicaState, clock:CClockReading) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     //requires CReplicaStateValid(replica)
//     requires Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica)
//     ensures  Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)),
//                                                                         replica', clock, packets_sent)
// {
//   var start_time := Time.GetDebugTimeTicks();

//     var newProposer := CProposerCheckForViewTimeout(replica.proposer, clock.t);
//     replica' := replica.(proposer := newProposer);
//     packets_sent := Broadcast(CBroadcastNop);
//     lemma_CReplicaNextReadClockCheckForViewTimeout(replica, clock, replica', packets_sent);

//     // var end_time := Time.GetDebugTimeTicks();
//     //     if(end_time >= start_time){
//     //       print end_time - start_time;
//     //       print "\n";
//     //     } else {
//     //       print("Wrong");
//     // }
// }

// lemma {:axiom} lemma_CReplicaNextReadClockCheckForViewTimeout(replica:ReplicaState, clock:CClockReading, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica)
//     ensures  Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)),
//                                                                             replica', clock, packets_sent)

// method CReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica:ReplicaState, clock:CClockReading) returns (replica':ReplicaState, packets_sent:OutboundPackets)
//     //requires CReplicaStateValid(replica)
//     requires Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica)
//     ensures  Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)),
//                                                                                     replica', clock, packets_sent)
// {
//   var start_time := Time.GetDebugTimeTicks();

//     var newProposer := CProposerCheckForQuorumOfViewSuspicions(replica.proposer, clock.t);
//     replica' := replica.(proposer := newProposer);
//     packets_sent := Broadcast(CBroadcastNop);
//     lemma_CReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica, clock, replica', packets_sent);

//     // var end_time := Time.GetDebugTimeTicks();
//     //     if(end_time >= start_time){
//     //       print end_time - start_time;
//     //       print "\n";
//     //     } else {
//     //       print("Wrong");
//     // }
// }

// lemma {:axiom} lemma_CReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica:ReplicaState, clock:CClockReading, replica':ReplicaState, packets_sent:OutboundPackets)
//     requires Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica)
//     ensures  Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(old(AbstractifyReplicaStateToLReplica(replica)),
//                                                                                     replica', clock, packets_sent)
}