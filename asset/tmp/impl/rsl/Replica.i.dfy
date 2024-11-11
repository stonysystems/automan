include ""


module Impl_LiveRSL__Replica_i 
{

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
	}

	predicate CReplicaIsAbstractable(s: CReplica) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CProposerIsAbstractable(s.proposer) 
		&& 
		CAcceptorIsAbstractable(s.acceptor) 
		&& 
		CLearnerIsAbstractable(s.learner) 
		&& 
		CExecutorIsAbstractable(s.executor)
	}

	function AbstractifyCReplicaToLReplica(s: CReplica) : LReplica 
		requires CReplicaIsAbstractable(s)
	{
		LReplica(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.nextHeartbeatTime, AbstractifyCProposerToLProposer(s.proposer), AbstractifyCAcceptorToLAcceptor(s.acceptor), AbstractifyCLearnerToLLearner(s.learner), AbstractifyCExecutorToLExecutor(s.executor))
	}

	function method CReplicaInit(c: CReplicaConstants) : CReplica 
		requires CReplicaConstantsIsValid(c)
		requires CWellFormedLConfiguration(c.all.config)
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

	function method CReplicaNextProcessInvalid(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Invalid?
		ensures var (s', non_empty_sequential_sent_packets) := CReplicaNextProcessInvalid(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(non_empty_sequential_sent_packets) && LReplicaNextProcessInvalid(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(non_empty_sequential_sent_packets))
	{
		var t1 := 
			s; 		
		var t2 := 
			[]; 		
		(t1, t2)
	}

	function method CReplicaNextProcessRequest(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Request?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
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
					[]; 				
				var t3 := 
					s.(proposer := t1); 				
				(t3, t2); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextProcess1a(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1a?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess1a(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CAcceptorProcess1a(s.acceptor, received_packet); 		
		var t2 := 
<<<<<<< HEAD
			s.(acceptor := t1.1); 		
		(t2, t1.0)
=======
			s.(acceptor := t1.0); 		
		(t2, t1.1)
>>>>>>> f0e13dcc7666fa3f27260947fdcb2879e4dc9ada
	}

	function method CReplicaNextProcess1b(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1b?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess1b(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess1b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if received_packet.src in s.proposer.constants.all.config.replica_ids && received_packet.msg.bal_1b == s.proposer.max_ballot_i_sent_1a && s.proposer.current_state == 1 && (forall other_packet :: other_packet in s.proposer.received_1b_packets ==> other_packet.src != received_packet.src) then 
				var t1 := 
					CProposerProcess1b(s.proposer, received_packet); 				
				var t2 := 
					CAcceptorTruncateLog(s.acceptor, received_packet.msg.log_truncation_point); 				
				var t3 := 
					[]; 				
				var t4 := 
					s.(proposer := t1, acceptor := t2); 				
				(t4, t3) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					[]; 				
				(t1, t2); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextProcessStartingPhase2(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_StartingPhase2?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessStartingPhase2(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessStartingPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CExecutorProcessStartingPhase2(s.executor, received_packet); 		
		var t2 := 
<<<<<<< HEAD
			s.(executor := t1.1); 		
		(t2, t1.0)
=======
			s.(executor := t1.0); 		
		(t2, t1.1)
>>>>>>> f0e13dcc7666fa3f27260947fdcb2879e4dc9ada
	}

	function method CReplicaNextProcess2a(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2a?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess2a(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			var m := 
				received_packet.msg; 			
			var t1 := 
				if received_packet.src in s.acceptor.constants.all.config.replica_ids && CBalLeq(s.acceptor.max_bal, m.bal_2a) && CLeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val) then 
					var t1 := 
						CAcceptorProcess2a(s.acceptor, received_packet); 					
					var t2 := 
<<<<<<< HEAD
						s.(acceptor := t1.1); 					
					(t2, t1.0) 
=======
						s.(acceptor := t1.0); 					
					(t2, t1.1) 
>>>>>>> f0e13dcc7666fa3f27260947fdcb2879e4dc9ada
				else 
					var t1 := 
						s; 					
					var t2 := 
						[]; 					
					(t1, t2); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextProcess2b(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2b?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess2b(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcess2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
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
							[]; 						
						var t3 := 
							s.(learner := t1); 						
						(t3, t2) 
					else 
						var t1 := 
							s; 						
						var t2 := 
							[]; 						
						(t1, t2); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextProcessReply(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Reply?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessReply(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessReply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			[]; 		
		var t2 := 
			s; 		
		(t2, t1)
	}

	function method CReplicaNextProcessAppStateSupply(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateSupply?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateSupply(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessAppStateSupply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if received_packet.src in s.executor.constants.all.config.replica_ids && received_packet.msg.opn_state_supply > s.executor.ops_complete then 
				var t1 := 
					CLearnerForgetOperationsBefore(s.learner, received_packet.msg.opn_state_supply); 				
				var t2 := 
					CExecutorProcessAppStateSupply(s.executor, received_packet); 				
				var t3 := 
					[]; 				
				var t4 := 
					s.(learner := t1, executor := t2); 				
				(t4, t3) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					[]; 				
				(t1, t2); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextProcessAppStateRequest(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateRequest?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateRequest(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessAppStateRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CExecutorProcessAppStateRequest(s.executor, received_packet); 		
		var t2 := 
<<<<<<< HEAD
			s.(executor := t1.1); 		
		(t2, t1.0)
=======
			s.(executor := t1.0); 		
		(t2, t1.1)
>>>>>>> f0e13dcc7666fa3f27260947fdcb2879e4dc9ada
	}

	function method CReplicaNextProcessHeartbeat(s: CReplica, received_packet: CPacket, clock: int) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Heartbeat?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessHeartbeat(s, received_packet, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), clock, AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerProcessHeartbeat(s.proposer, received_packet, clock); 		
		var t2 := 
			CAcceptorProcessHeartbeat(s.acceptor, received_packet); 		
		var t3 := 
			[]; 		
		var t4 := 
			s.(proposer := t1, acceptor := t2); 		
		(t4, t3)
	}

	function method CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerMaybeEnterNewViewAndSend1a(s.proposer); 		
		var t2 := 
<<<<<<< HEAD
			s.(proposer := t1.1); 		
		(t2, t1.0)
=======
			s.(proposer := t1.0); 		
		(t2, t1.1)
>>>>>>> f0e13dcc7666fa3f27260947fdcb2879e4dc9ada
	}

	function method CReplicaNextSpontaneousMaybeEnterPhase2(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterPhase2(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeEnterPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerMaybeEnterPhase2(s.proposer, s.acceptor.log_truncation_point); 		
		var t2 := 
<<<<<<< HEAD
			s.(proposer := t1.1); 		
		(t2, t1.0)
=======
			s.(proposer := t1.0); 		
		(t2, t1.1)
>>>>>>> f0e13dcc7666fa3f27260947fdcb2879e4dc9ada
	}

	function method CReplicaNextReadClockMaybeNominateValueAndSend2a(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeNominateValueAndSend2a(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextReadClockMaybeNominateValueAndSend2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerMaybeNominateValueAndSend2a(s.proposer, clock.t, s.acceptor.log_truncation_point); 		
		var t2 := 
<<<<<<< HEAD
			s.(proposer := t1.1); 		
		(t2, t1.0)
	}

	function method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s: CReplica, s': CReplica, sent_packets: OutboundPackets) : bool 
		requires CReplicaIsValid(s)
		requires CReplicaIsValid(s')
		requires OutboundPacketsIsValid(sent_packets)
		ensures var lr := LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets)); var cr := CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sent_packets); (cr) == (lr)
	{
		(exists opn :: opn in s.acceptor.last_checkpointed_operation && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) && if opn > s.acceptor.log_truncation_point then CAcceptorTruncateLog(s.acceptor, s'.acceptor, opn) && s' == s.(acceptor := s'.acceptor) && sent_packets == [] else s' == s && sent_packets == [])
=======
			s.(proposer := t1.0); 		
		(t2, t1.1)
>>>>>>> f0e13dcc7666fa3f27260947fdcb2879e4dc9ada
	}

	function method CReplicaNextSpontaneousMaybeMakeDecision(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeMakeDecision(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeMakeDecision(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
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
						[]; 					
					(t2, t3) 
				else 
					var t1 := 
						s; 					
					var t2 := 
						[]; 					
					(t1, t2); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextSpontaneousMaybeExecute(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if s.executor.next_op_to_execute.COutstandingOpKnown? && CtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) && CReplicaConstantsValid(s.executor.constants) then 
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
<<<<<<< HEAD
						s.(proposer := t1, learner := t2, executor := t3.1); 					
					(t4, t3.0); 				
=======
						s.(proposer := t1, learner := t2, executor := t3.0); 					
					(t4, t3.1); 				
>>>>>>> f0e13dcc7666fa3f27260947fdcb2879e4dc9ada
				(t1.1, t1.0) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					[]; 				
				(t1, t2); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextReadClockMaybeSendHeartbeat(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextReadClockMaybeSendHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if clock.t < s.nextHeartbeatTime then 
				var t1 := 
					s; 				
				var t2 := 
					[]; 				
				(t1, t2) 
			else 
				var t1 := 
					UpperBoundedAdditionImpl(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val); 				
				var t2 := 
					BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete)); 				
				var t3 := 
					s.(nextHeartbeatTime := t1); 				
				(t3, t2); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextReadClockCheckForViewTimeout(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForViewTimeout(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextReadClockCheckForViewTimeout(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForViewTimeout(s.proposer, clock.t); 		
		var t2 := 
			[]; 		
		var t3 := 
			s.(proposer := t1); 		
		(t3, t2)
	}

	function method CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForQuorumOfViewSuspicions(s.proposer, clock.t); 		
		var t2 := 
			[]; 		
		var t3 := 
			s.(proposer := t1); 		
		(t3, t2)
	}
}
