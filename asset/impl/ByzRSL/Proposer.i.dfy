/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__Proposer_i

[Action] LProposerInit
Check passed

[Action] LProposerProcessRequest
Check passed

[Action] LProposerMaybeEnterNewViewAndSend1a
Check passed

[Action] LProposerProcess1b
Check passed

[Action] LProposerMaybeEnterPhase2
Check passed

[Action] LProposerNominateNewValueAndSend1c
Check passed

[Action] LProposerMaybeNominateValueAndSend1c
Check passed

[Action] LProposerProcessHeartbeat
Check passed

[Action] LProposerCheckForViewTimeout
Check passed

[Action] LProposerCheckForQuorumOfViewSuspicions
Check passed

[Action] LProposerResetViewTimerDueToExecution
Check passed
**********************************************************************/

include ""


module Impl_LiveByzRSL__Proposer_i 
{

	datatype CIncompleteBatchTimer = 
	CIncompleteBatchTimerOn(
		when: int
	)
	 | 
	CIncompleteBatchTimerOff(
		
	)

	predicate CIncompleteBatchTimerIsValid(s: CIncompleteBatchTimer) 
	{
		match s
		case CIncompleteBatchTimerOn(when) => CIncompleteBatchTimerIsAbstractable(s)
		case CIncompleteBatchTimerOff() => CIncompleteBatchTimerIsAbstractable(s)

	}

	predicate CIncompleteBatchTimerIsAbstractable(s: CIncompleteBatchTimer) 
	{
		match s
		case CIncompleteBatchTimerOn(when) => true
		case CIncompleteBatchTimerOff() => true

	}

	function AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(s: CIncompleteBatchTimer) : IncompleteBatchTimer 
		requires CIncompleteBatchTimerIsAbstractable(s)
	{
		match s
		case CIncompleteBatchTimerOn(when) => IncompleteBatchTimerOn(s.when)
		case CIncompleteBatchTimerOff() => IncompleteBatchTimerOff()

	}

	datatype CProposer = 
	CProposer(
		constants: CReplicaConstants, 
		current_state: int, 
		request_queue: seq<CRequest>, 
		max_ballot_i_sent_1a: CBallot, 
		next_operation_number_to_propose: int, 
		received_1b_packets: OutboundPackets, 
		highest_seqno_requested_by_client_this_view: map<EndPoint, int>, 
		incomplete_batch_timer: CIncompleteBatchTimer, 
		election_state: CElectionState
	)

	predicate CProposerIsValid(s: CProposer) 
	{
		CProposerIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		(forall i :: i in s.request_queue ==> CRequestIsValid(i)) 
		&& 
		CBallotIsValid(s.max_ballot_i_sent_1a) 
		&& 
		OutboundPacketsIsValid(s.received_1b_packets) 
		&& 
		(forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsValid(i)) 
		&& 
		CIncompleteBatchTimerIsValid(s.incomplete_batch_timer) 
		&& 
		CElectionStateIsValid(s.election_state)
	}

	predicate CProposerIsAbstractable(s: CProposer) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		(forall i :: i in s.request_queue ==> CRequestIsAbstractable(i)) 
		&& 
		CBallotIsAbstractable(s.max_ballot_i_sent_1a) 
		&& 
		OutboundPacketsIsAbstractable(s.received_1b_packets) 
		&& 
		(forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsAbstractable(i)) 
		&& 
		CIncompleteBatchTimerIsAbstractable(s.incomplete_batch_timer) 
		&& 
		CElectionStateIsAbstractable(s.election_state)
	}

	function AbstractifyCProposerToLProposer(s: CProposer) : LProposer 
		requires CProposerIsAbstractable(s)
	{
		LProposer(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.current_state, AbstractifySeq(s.request_queue, AbstractifyCRequestToRequest), AbstractifyCBallotToBallot(s.max_ballot_i_sent_1a), s.next_operation_number_to_propose, AbstractifyOutboundCPacketsToSeqOfRslPackets(s.received_1b_packets), AbstractifyMap(s.highest_seqno_requested_by_client_this_view, AbstractifyEndPointToNodeIdentity, NoChange, AbstractifyNodeIdentityToEndPoint), AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(s.incomplete_batch_timer), AbstractifyCElectionStateToElectionState(s.election_state))
	}

	function method CIsAfterLogTruncationPoint(opn: COperationNumber, S: OutboundPackets) : bool 
		requires COperationNumberIsValid(opn)
		requires OutboundPacketsIsValid(S)
		ensures var lr := LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyOutboundCPacketsToSeqOfRslPackets(S)); var cr := CIsAfterLogTruncationPoint(opn, S); (cr) == (lr)
	{
		(forall p :: p in S && p.msg.CMessage_1b? ==> p.msg.log_truncation_point <= opn)
	}

	function method CProposerCanNominateUsingOperationNumber(s: CProposer, log_truncation_point: COperationNumber, opn: COperationNumber) : bool 
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		requires COperationNumberIsValid(opn)
		ensures var lr := LProposerCanNominateUsingOperationNumber(AbstractifyCProposerToLProposer(s), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CProposerCanNominateUsingOperationNumber(s, log_truncation_point, opn); (cr) == (lr)
	{
		s.election_state.current_view == s.max_ballot_i_sent_1a 
		&& 
		s.current_state == 2 
		&& 
		|s.received_1b_packets| >= CByzQuorumSize(s.constants.all.config) 
		&& 
		CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) 
		&& 
		CIsAfterLogTruncationPoint(opn, s.received_1b_packets) 
		&& 
		opn < UpperBoundedAdditionImpl(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val) 
		&& 
		opn >= 0 
		&& 
		CtUpperBound(opn, s.constants.all.params.max_integer_val)
	}

	function method CProposerInit(c: CReplicaConstants) : CProposer 
		requires CReplicaConstantsIsValid(c)
		requires CWellFormedLConfiguration(c.all.config)
		ensures var s := CProposerInit(c); CProposerIsValid(s) && LProposerInit(AbstractifyCProposerToLProposer(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			0; 		
		var t3 := 
			[]; 		
		var t4 := 
			CBallot(0, c.my_index); 		
		var t5 := 
			0; 		
		var t6 := 
			[]; 		
		var t7 := 
			map[]; 		
		var t8 := 
			CElectionStateInit(c); 		
		var t9 := 
			CIncompleteBatchTimerOff(); 		
		CProposer(t1, t2, t3, t4, t5, t6, t7, t9, t8)
	}

	function method CProposerProcessRequest(s: CProposer, packet: CPacket) : CProposer 
		requires CProposerIsValid(s)
		requires CPacketIsValid(packet)
		requires packet.msg.CMessage_Request?
		ensures var s' := CProposerProcessRequest(s, packet); CProposerIsValid(s') && LProposerProcessRequest(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(packet))
	{
		var t1 := 
			var val := 
				CRequest(packet.src, packet.msg.seqno_req, packet.msg.val); 			
			var t1 := 
				CElectionStateReflectReceivedRequest(s.election_state, val); 			
			var t2 := 
				if s.current_state != 0 && ((val.client !in s.highest_seqno_requested_by_client_this_view) || (val.seqno > s.highest_seqno_requested_by_client_this_view[val.client])) then 
					var t1 := 
						s.(election_state := t1, request_queue := s.request_queue + [val], highest_seqno_requested_by_client_this_view := s.highest_seqno_requested_by_client_this_view[val.client := val.seqno]); 					
					t1 
				else 
					var t1 := 
						s.(election_state := t1); 					
					t1; 			
			t2; 		
		t1
	}

	function method CProposerMaybeEnterNewViewAndSend1a(s: CProposer) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		ensures var (s', sent_packets) := CProposerMaybeEnterNewViewAndSend1a(s); CProposerIsValid(s') && OutboundPacketsIsValid(sent_packets) && LProposerMaybeEnterNewViewAndSend1a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			if s.election_state.current_view.proposer_id == s.constants.my_index && CBalLt(s.max_ballot_i_sent_1a, s.election_state.current_view) then 
				var t1 := 
					s.(current_state := 1, max_ballot_i_sent_1a := s.election_state.current_view, received_1b_packets := [], highest_seqno_requested_by_client_this_view := map[], request_queue := s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch); 				
				var t2 := 
					BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1a(s.election_state.current_view)); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					[]; 				
				(t1, t2); 		
		(t1.1, t1.0)
	}

	function method CProposerProcess1b(s: CProposer, p: CPacket) : CProposer 
		requires CProposerIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_1b?
		requires p.src in s.constants.all.config.replica_ids
		requires p.msg.bal_1b == s.max_ballot_i_sent_1a
		requires s.current_state == 1
		requires (forall other_packet :: other_packet in s.received_1b_packets ==> other_packet.src != p.src)
		ensures var s' := CProposerProcess1b(s, p); CProposerIsValid(s') && LProposerProcess1b(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p))
	{
		var t1 := 
			s.(received_1b_packets := s.received_1b_packets + [p]); 		
		t1
	}

	function method CProposerMaybeEnterPhase2(s: CProposer, log_truncation_point: COperationNumber) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var (s', sent_packets) := CProposerMaybeEnterPhase2(s, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(sent_packets) && LProposerMaybeEnterPhase2(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			if |s.received_1b_packets| >= CByzQuorumSize(s.constants.all.config) && CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) && s.current_state == 1 then 
				var t1 := 
					s.(current_state := 2, next_operation_number_to_propose := log_truncation_point); 				
				var t2 := 
					BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_StartingPhase2(s.max_ballot_i_sent_1a, log_truncation_point)); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					[]; 				
				(t1, t2); 		
		(t1.1, t1.0)
	}

	function method CProposerNominateNewValueAndSend1c(s: CProposer, clock: int, log_truncation_point: COperationNumber) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
		requires CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
		ensures var (s', sent_packets) := CProposerNominateNewValueAndSend1c(s, clock, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(sent_packets) && LProposerNominateNewValueAndSend1c(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			var batchSize := 
				if (|s.request_queue| <= s.constants.all.params.max_batch_size) || (s.constants.all.params.max_batch_size < 0) then 
					|s.request_queue| 
				else 
					s.constants.all.params.max_batch_size; 			
			var t1 := 
				var v := 
					s.request_queue[ .. batchSize]; 				
				var t1 := 
					var opn := 
						s.next_operation_number_to_propose; 					
					var t1 := 
						s.(request_queue := s.request_queue[batchSize .. ], next_operation_number_to_propose := s.next_operation_number_to_propose + 1, incomplete_batch_timer := if |s.request_queue| > batchSize then CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)) else CIncompleteBatchTimerOff()); 					
					var t2 := 
						BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1c(s.max_ballot_i_sent_1a, opn, v)); 					
					(t1, t2); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CProposerNominateOldValueAndSend1c(s: CProposer, log_truncation_point: COperationNumber) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
		requires !(CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose))
		ensures var (s', sent_packets) := CProposerNominateOldValueAndSend1c(s, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(sent_packets) && LProposerNominateOldValueAndSend1c(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		
	}

	function method CProposerMaybeNominateValueAndSend1c(s: CProposer, clock: int, log_truncation_point: int) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		ensures var (s', sent_packets) := CProposerMaybeNominateValueAndSend1c(s, clock, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(sent_packets) && LProposerMaybeNominateValueAndSend1c(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock, log_truncation_point, AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			if !(CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)) then 
				var t1 := 
					s; 				
				var t2 := 
					[]; 				
				(t1, t2) 
			else 
				var t1 := 
					if !(CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)) then 
						var t1 := 
							CProposerNominateOldValueAndSend1c(s, log_truncation_point); 						
						(t1.0, t1.1) 
					else 
						var t1 := 
							if (|s.request_queue| >= s.constants.all.params.max_batch_size) || (|s.request_queue| > 0 && s.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= s.incomplete_batch_timer.when) then 
								var t1 := 
									CProposerNominateNewValueAndSend1c(s, clock, log_truncation_point); 								
								(t1.0, t1.1) 
							else 
								var t1 := 
									if |s.request_queue| > 0 && s.incomplete_batch_timer.CIncompleteBatchTimerOff? then 
										var t1 := 
											s.(incomplete_batch_timer := CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val))); 										
										var t2 := 
											[]; 										
										(t1, t2) 
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

	function method CProposerProcessHeartbeat(s: CProposer, p: CPacket, clock: int) : CProposer 
		requires CProposerIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_Heartbeat?
		ensures var s' := CProposerProcessHeartbeat(s, p, clock); CProposerIsValid(s') && LProposerProcessHeartbeat(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p), clock)
	{
		var t1 := 
			CElectionStateProcessHeartbeat(s.election_state, p, clock); 		
		var t2 := 
			if CBalLt(s.election_state.current_view, holder.current_view) then 
				var t1 := 
					0; 				
				var t2 := 
					[]; 				
				(t1, t2) 
			else 
				var t1 := 
					s.current_state; 				
				var t2 := 
					s.request_queue; 				
				(t1, t2); 		
		var t3 := 
			s.(election_state := t1, current_state := t2.1, request_queue := t2.0); 		
		t3
	}

	function method CProposerCheckForViewTimeout(s: CProposer, clock: int) : CProposer 
		requires CProposerIsValid(s)
		ensures var s' := CProposerCheckForViewTimeout(s, clock); CProposerIsValid(s') && LProposerCheckForViewTimeout(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	{
		var t1 := 
			CElectionStateCheckForViewTimeout(s.election_state, clock); 		
		var t2 := 
			s.(election_state := t1); 		
		t2
	}

	function method CProposerCheckForQuorumOfViewSuspicions(s: CProposer, clock: int) : CProposer 
		requires CProposerIsValid(s)
		ensures var s' := CProposerCheckForQuorumOfViewSuspicions(s, clock); CProposerIsValid(s') && LProposerCheckForQuorumOfViewSuspicions(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	{
		var t1 := 
			CElectionStateCheckForQuorumOfViewSuspicions(s.election_state, clock); 		
		var t2 := 
			if CBalLt(s.election_state.current_view, holder.current_view) then 
				var t1 := 
					0; 				
				var t2 := 
					[]; 				
				(t1, t2) 
			else 
				var t1 := 
					s.current_state; 				
				var t2 := 
					s.request_queue; 				
				(t1, t2); 		
		var t3 := 
			s.(election_state := t1, current_state := t2.1, request_queue := t2.0); 		
		t3
	}

	function method CProposerResetViewTimerDueToExecution(s: CProposer, val: CRequestBatch) : CProposer 
		requires CProposerIsValid(s)
		requires CRequestBatchIsValid(val)
		ensures var s' := CProposerResetViewTimerDueToExecution(s, val); CProposerIsValid(s') && LProposerResetViewTimerDueToExecution(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCRequestBatchToRequestBatch(val))
	{
		var t1 := 
			CElectionStateReflectExecutedRequestBatch(s.election_state, val); 		
		var t2 := 
			s.(election_state := t1); 		
		t2
	}
}
