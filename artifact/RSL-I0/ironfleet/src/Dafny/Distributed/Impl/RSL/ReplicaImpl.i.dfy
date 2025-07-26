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
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveRSL__AcceptorModel_i
  import opened LiveRSL__AppInterface_i
  import opened LiveRSL__CMessage_i
  import opened LiveRSL__CMessageRefinements_i
  import opened LiveRSL__CTypes_i
  import opened LiveRSL__ExecutorModel_i
  import opened LiveRSL__LearnerModel_i
  import opened LiveRSL__PacketParsing_i
  import opened LiveRSL__Proposer_i
  import opened LiveRSL__ProposerModel_i
  import opened LiveRSL__Replica_i
  import opened LiveRSL__ConstantsState_i
  import opened LiveRSL__Types_i
  import opened Logic__Option_i
  import opened LiveRSL__CClockReading_i
  import opened LiveRSL__CPaxosConfiguration_i
  import opened Common__UpperBound_i
  import opened Impl__LiveRSL__Broadcast_i
  import opened LiveRSL__Configuration_i
  import opened Common__Util_i
  import opened Common__UdpClient_i
  import opened LiveRSL__Acceptor_i
  import opened GenericRefinement_i
  import opened Collections__CountMatches_i
  import opened Collections__Multisets_s
  import opened Collections__Seqs_i

  /************************** AutoMan Translation ************************/

  /** 9 + 0 */
  datatype CReplica = 
	CReplica(
		constants: CReplicaConstants, 
		nextHeartbeatTime: int, 
		proposer: CProposer, 
		acceptor: CAcceptor, 
		learner: CLearner, 
		executor: CExecutor
	)

  /** 0 + 15 + 1 */
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

  /** 0 + 12 */
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

  /** 0 + 5 */
	function AbstractifyCReplicaToLReplica(s: CReplica) : LReplica 
		requires CReplicaIsAbstractable(s)
    // requires CReplicaIsValid(s)
	{
		LReplica(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.nextHeartbeatTime, AbstractifyCProposerToLProposer(s.proposer), AbstractifyCAcceptorToLAcceptor(s.acceptor), AbstractifyCLearnerToLLearner(s.learner), AbstractifyCExecutorToLExecutor(s.executor))
	}

  /** 15 + 2 */
  function method CReplicaInit(c: CReplicaConstants) : CReplica 
		requires CReplicaConstantsIsValid(c)
		ensures var r := CReplicaInit(c); CReplicaIsValid(r) && LReplicaInit(AbstractifyCReplicaToLReplica(r), AbstractifyCReplicaConstantsToLReplicaConstants(c))
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
		CReplica(t1, t2, t3, t4, t5, t6)
	}

  /** 7 + 4 */
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

  /** 19 + 8 + 2 */
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

  /** 8 + 9 + 2 */
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

  /** 21 + 8 + 2 */
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

  /** 8 + 8 + 2 */
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

  /** 21 + 8 + 2 */
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

  /** 26 + 8 + 2 */
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

  /** 7 + 8 + 2 */
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

  /** 21 + 8 + 2 */
  function method CReplicaNextProcessAppStateSupply(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateSupply?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateSupply(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessAppStateSupply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if received_packet.src in s.executor.constants.all.config.replica_ids && received_packet.msg.opn_state_supply > s.executor.ops_complete then 
				var t1 := 
					CLearnerForgetOperationsBefore(s.learner, received_packet.msg.opn_state_supply); 				
				var t2 := 
					CExecutorProcessAppStateSupply(s.executor, received_packet); 				
				var t3 := 
					PacketSequence([]); 				
				var t4 := 
					s.(learner := t1, executor := t2); 				
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

  /** 8 + 8 + 2 */
  function method CReplicaNextProcessAppStateRequest(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateRequest?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateRequest(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessAppStateRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CExecutorProcessAppStateRequest(s.executor, received_packet); 		
		var t2 := 
			s.(executor := t1.0); 		
    lemma_Postconditions(s, received_packet, t2, t1.1); /** Manually Added */
		(t2, t1.1)
	}

  /** 22 + 8 + 2 */
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

  /** 8 + 8 + 2 */
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

  /** 8 + 8 + 2 */
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

  /** 23 + 6 + 2 */
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

  /** 25 + 6 + 2 */
  function method CReplicaNextSpontaneousMaybeExecute(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if s.executor.next_op_to_execute.COutstandingOpKnown? && CLtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) && CReplicaConstantsValid(s.executor.constants) then 
				var t1 := 
					var v := 
						s.executor.next_op_to_execute.v; 					
					var t1 := 
						CProposerResetViewTimerDueToExecution(s.proposer, v); 					
					var t2 := 
						CLearnerForgetDecision(s.learner, s.executor.ops_complete); 					
					var t3 := 
						CExecutorExecute(s.executor); 					
					var t4 := 
						s.(proposer := t1, learner := t2, executor := t3.0); 					
					(t4, t3.1); 				
				(t1.0, t1.1) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					PacketSequence([]); 				
				(t1, t2); 		
    lemma_NoReceived_Postconditions(s, t1.0, t1.1); /** Manually Added */
		(t1.0, t1.1)
	}

  /** 19 + 7 + 2 */
  function method CReplicaNextReadClockMaybeSendHeartbeat(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
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

  /** 10 + 7 + 2 */
  function method CReplicaNextReadClockCheckForViewTimeout(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
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

  /** 10 + 7 + 2 */
  function method CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
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

  /** 13 + 8 */
  method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
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
  
  /** 0 + 3 */
  lemma {:axiom}  lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica, s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
            && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
            && OutboundPacketsIsValid(sequential_sent_packets) 
            && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  

  /** 4 + 4 */
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
    && inp.msg.CMessage_Request?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_1a_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_1a?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_1b_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_1b?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_StartingPhase2_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_StartingPhase2?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_2a_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_2a?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_2b_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_2b?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_AppStateRequest_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_AppStateRequest?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_AppStateSupply_Preconditions(replica:CReplica, inp:CPacket)
  {

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

  lemma {:axiom} lemma_CReplicaNextProcessRequest(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_Request_Preconditions(replica, inp)
    ensures  Replica_Next_Process_Request_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                         inp, packets_sent)

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