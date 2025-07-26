/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__Replica_i

[Action] LReplicaInit
Check passed

[Action] LReplicaNextProcessInvalid
Check passed

[Action] LReplicaNextProcessRequest
Check passed

[Action] LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a
Check passed

[Action] LReplicaNextProcess1a
Check passed

[Action] LReplicaNextProcess1b
Check passed

[Action] LReplicaNextSpontaneousMaybeEnterPhase2
Check passed

[Action] LReplicaNextProcessStartingPhase2
Check passed

[Action] LReplicaNextReadClockMaybeNominateValueAndSend1c
Check passed

[Action] LReplicaNextProcess1c
Check passed

[Action] LReplicaNextProcess2av
Check passed

[Action] LReplicaNextSpontaneousMaybeSend2b
Check passed

[Action] LReplicaNextProcess2b
Check passed

[Action] LReplicaNextProcessReply
Check passed

[Action] LReplicaNextProcessAppStateSupply
Check passed

[Action] LReplicaNextProcessAppStateRequest
Check passed

[Action] LReplicaNextProcessHeartbeat
Check passed

[Action] LReplicaNextSpontaneousMaybeExecute
Check passed

[Action] LReplicaNextReadClockMaybeSendHeartbeat
Check passed

[Action] LReplicaNextReadClockCheckForViewTimeout
Check passed

[Action] LReplicaNextReadClockCheckForQuorumOfViewSuspicions
Check passed
**********************************************************************/

include ""


module Impl_LiveByzRSL__Replica_i 
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
		ensures var (s', sent_packets) := CReplicaNextProcessInvalid(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcessInvalid(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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
		ensures var (s', sent_packets) := CReplicaNextProcessRequest(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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

	function method CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			CProposerMaybeEnterNewViewAndSend1a(s.proposer); 		
		var t2 := 
			CAcceptorMaybeEnterNewView(s.acceptor); 		
		var t3 := 
			s.(proposer := t1.0, acceptor := t2); 		
		(t3, t1.1)
	}

	function method CReplicaNextProcess1a(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1a?
		ensures var (s', sent_packets) := CReplicaNextProcess1a(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcess1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			CAcceptorProcess1a(s.acceptor, received_packet); 		
		var t2 := 
			s.(acceptor := t1.0); 		
		(t2, t1.1)
	}

	function method CReplicaNextProcess1b(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1b?
		ensures var (s', sent_packets) := CReplicaNextProcess1b(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcess1b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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
					if received_packet.src in s.acceptor.constants.all.config.replica_ids && (forall other_packet :: other_packet in s.acceptor.received_1b_packets ==> other_packet.src != received_packet.src) then 
						var t1 := 
							CAcceptorProcess1b(s.acceptor, received_packet); 						
						var t2 := 
							s.(acceptor := t1); 						
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

	function method CReplicaNextSpontaneousMaybeEnterPhase2(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sent_packets) := CReplicaNextSpontaneousMaybeEnterPhase2(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextSpontaneousMaybeEnterPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			CProposerMaybeEnterPhase2(s.proposer, s.acceptor.log_truncation_point); 		
		var t2 := 
			s.(proposer := t1.0); 		
		(t2, t1.1)
	}

	function method CReplicaNextProcessStartingPhase2(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_StartingPhase2?
		ensures var (s', sent_packets) := CReplicaNextProcessStartingPhase2(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcessStartingPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			CExecutorProcessStartingPhase2(s.executor, received_packet); 		
		var t2 := 
			s.(executor := t1.0); 		
		(t2, t1.1)
	}

	function method CReplicaNextReadClockMaybeNominateValueAndSend1c(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CClockReadingIsValid(clock)
		ensures var (s', sent_packets) := CReplicaNextReadClockMaybeNominateValueAndSend1c(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextReadClockMaybeNominateValueAndSend1c(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			CProposerMaybeNominateValueAndSend1c(s.proposer, clock.t, s.acceptor.log_truncation_point); 		
		var t2 := 
			s.(proposer := t1.0); 		
		(t2, t1.1)
	}

	function method CReplicaNextProcess1c(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1c?
		ensures var (s', sent_packets) := CReplicaNextProcess1c(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcess1c(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			var m := 
				received_packet.msg; 			
			var t1 := 
				var packets_1b := 
					s.acceptor.received_1b_packets; 				
				var t1 := 
					var byzq := 
						CByzQuorumSize(s.constants.all.config); 					
					var t1 := 
						var wq := 
							CMinQuorumSize(s.constants.all.config); 						
						var t1 := 
							var req_is_valid_from_client := 
								(forall req :: req in m.val_1c ==> CCheckRequestValid(s.proposer.election_state, req)); 							
							var t1 := 
								var req_is_safe := 
									if s.proposer.current_state == 2 then 
										true 
									else 
										if CSeqOfMessage1b(packets_1b) then 
											(CAllAcceptorsHadNoProposal(packets_1b, m.opn_1c)) || (CValIsSafeAt(m.val_1c, packets_1b, m.opn_1c, byzq, wq)) 
										else 
											false; 								
								var t1 := 
									if received_packet.src in s.acceptor.constants.all.config.replica_ids && req_is_valid_from_client && req_is_safe && CBalLeq(s.acceptor.max_bal, m.bal_1c) && CLeqUpperBound(m.opn_1c, s.acceptor.constants.all.params.max_integer_val) then 
										var t1 := 
											CAcceptorProcess1c(s.acceptor, received_packet); 										
										var t2 := 
											s.(acceptor := t1.0); 										
										(t2, t1.1) 
									else 
										var t1 := 
											s; 										
										var t2 := 
											[]; 										
										(t1, t2); 								
								(t1.1, t1.0); 							
							(t1.1, t1.0); 						
						(t1.1, t1.0); 					
					(t1.1, t1.0); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextProcess2av(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2av?
		ensures var (s', sent_packets) := CReplicaNextProcess2av(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcess2av(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			var opn := 
				received_packet.msg.opn_2av; 			
			var t1 := 
				var src := 
					received_packet.src; 				
				var t1 := 
					var op_sendable := 
						(s.acceptor.opn_to_be_send_2b < opn) || (s.acceptor.opn_to_be_send_2b == opn && s.acceptor.val_to_be_sent_2b.CValToBeSent2bUnknown?); 					
					var t1 := 
						if op_sendable && src in s.acceptor.constants.all.config.replica_ids then 
							var t1 := 
								CAcceptorProcess2av(s.acceptor, received_packet); 							
							var t2 := 
								s.(acceptor := t1); 							
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
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextSpontaneousMaybeSend2b(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sent_packets) := CReplicaNextSpontaneousMaybeSend2b(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextSpontaneousMaybeSend2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			if s.acceptor.val_to_be_sent_2b.CValToBeSent2bKnown? && s.acceptor.val_to_be_sent_2b.bal == s.acceptor.max_bal then 
				var t1 := 
					CAcceptorSent2b(s.acceptor); 				
				var t2 := 
					s.(acceptor := t1.0); 				
				(t2, t1.1) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					[]; 				
				(t1, t2); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextProcess2b(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2b?
		ensures var (s', sent_packets) := CReplicaNextProcess2b(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcess2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			var opn := 
				received_packet.msg.opn_2b; 			
			var t1 := 
				var src := 
					received_packet.src; 				
				var t1 := 
					var op_learnable := 
						(s.executor.ops_complete < opn) || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.COutstandingOpUnknown?); 					
					var t1 := 
						if op_learnable && src in s.learner.constants.all.config.replica_ids then 
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
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CReplicaNextProcessReply(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Reply?
		ensures var (s', sent_packets) := CReplicaNextProcessReply(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcessReply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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
		ensures var (s', sent_packets) := CReplicaNextProcessAppStateSupply(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcessAppStateSupply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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
		ensures var (s', sent_packets) := CReplicaNextProcessAppStateRequest(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcessAppStateRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			CExecutorProcessAppStateRequest(s.executor, received_packet); 		
		var t2 := 
			s.(executor := t1.0); 		
		(t2, t1.1)
	}

	function method CReplicaNextProcessHeartbeat(s: CReplica, received_packet: CPacket, clock: int) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Heartbeat?
		ensures var (s', sent_packets) := CReplicaNextProcessHeartbeat(s, received_packet, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextProcessHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), clock, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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

	function method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sent_packets) := CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		
	}

	function method CReplicaNextSpontaneousMaybeExecute(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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
						CAcceptorForgetReceived2avs(s.acceptor, s.executor.ops_complete); 					
					var t4 := 
						CExecutorExecute(s.executor); 					
					var t5 := 
						s.(acceptor := t3, proposer := t1, learner := t2, executor := t4.0); 					
					(t5, t4.1); 				
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
		ensures var (s', sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextReadClockMaybeSendHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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
		ensures var (s', sent_packets) := CReplicaNextReadClockCheckForViewTimeout(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextReadClockCheckForViewTimeout(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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
		ensures var (s', sent_packets) := CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, clock); CReplicaIsValid(s') && OutboundPacketsIsValid(sent_packets) && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
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
