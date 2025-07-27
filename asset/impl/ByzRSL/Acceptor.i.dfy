/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__Acceptor_i

[Action] RemoveVotesBeforeLogTruncationPoint
Check passed

[Action] LAddVoteAndRemoveOldOnes
Check passed

[Action] LAcceptorInit
Check passed

[Action] LAcceptorMaybeEnterNewView
Check passed

[Action] LAcceptorProcess1a
Check passed

[Action] LAcceptorProcess1b
Check passed

[Action] LAcceptorProcess1c
Check passed

[Action] LAcceptorProcess2av
Check passed

[Action] LAcceptorDecide2bVal
Check passed

[Action] LAcceptorSent2b
Check passed

[Action] LAcceptorForgetReceived2avs
Check passed

[Action] LAcceptorProcessHeartbeat
Check passed

[Action] LAcceptorTruncateLog
Check passed
**********************************************************************/

include ""


module Impl_LiveByzRSL__Acceptor_i 
{

	datatype CAcceptorTuple = 
	CAcceptorTuple(
		received_2av_packets: OutboundPackets
	)

	predicate CAcceptorTupleIsValid(s: CAcceptorTuple) 
	{
		CAcceptorTupleIsAbstractable(s) 
		&& 
		OutboundPacketsIsValid(s.received_2av_packets)
	}

	predicate CAcceptorTupleIsAbstractable(s: CAcceptorTuple) 
	{
		OutboundPacketsIsAbstractable(s.received_2av_packets)
	}

	function AbstractifyCAcceptorTupleToAcceptorTuple(s: CAcceptorTuple) : AcceptorTuple 
		requires CAcceptorTupleIsAbstractable(s)
	{
		AcceptorTuple(AbstractifyOutboundCPacketsToSeqOfRslPackets(s.received_2av_packets))
	}
	type CReceived2avs = map<COperationNumber, CAcceptorTuple>

	predicate CReceived2avsIsAbstractable(s: CReceived2avs) 
	{
		(forall i :: i in s ==> COperationNumberIsAbstractable(i) && CAcceptorTupleIsAbstractable(s[i]))
	}

	predicate CReceived2avsIsValid(s: CReceived2avs) 
	{
		CReceived2avsIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CAcceptorTupleIsValid(s[i]))
	}

	function AbstractifyCReceived2avsToReceived2avs(s: CReceived2avs) : Received2avs 
		requires CReceived2avsIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyCOperationNumberToOperationNumber, AbstractifyAcceptorTupleToCAcceptorTuple, AbstractifyOperationNumberToCOperationNumber)
	}

	datatype CValToBeSent2b = 
	CValToBeSent2bKnown(
		v: CRequestBatch, 
		bal: CBallot
	)
	 | 
	CValToBeSent2bUnknown(
		
	)

	predicate CValToBeSent2bIsValid(s: CValToBeSent2b) 
	{
		match s
		case CValToBeSent2bKnown(v, bal) => CValToBeSent2bIsAbstractable(s) && CRequestBatchIsValid(s.v) && CBallotIsValid(s.bal)
		case CValToBeSent2bUnknown() => CValToBeSent2bIsAbstractable(s)

	}

	predicate CValToBeSent2bIsAbstractable(s: CValToBeSent2b) 
	{
		match s
		case CValToBeSent2bKnown(v, bal) => CRequestBatchIsAbstractable(s.v) && CBallotIsAbstractable(s.bal)
		case CValToBeSent2bUnknown() => true

	}

	function AbstractifyCValToBeSent2bToValToBeSent2b(s: CValToBeSent2b) : ValToBeSent2b 
		requires CValToBeSent2bIsAbstractable(s)
	{
		match s
		case CValToBeSent2bKnown(v, bal) => ValToBeSent2bKnown(AbstractifyCRequestBatchToRequestBatch(s.v), AbstractifyCBallotToBallot(s.bal))
		case CValToBeSent2bUnknown() => ValToBeSent2bUnknown()

	}

	datatype CAcceptor = 
	CAcceptor(
		constants: CReplicaConstants, 
		max_bal: CBallot, 
		votes: CVotes, 
		last_checkpointed_operation: seq<COperationNumber>, 
		log_truncation_point: COperationNumber, 
		received_1b_packets: OutboundPackets, 
		received_2avs: CReceived2avs, 
		opn_to_be_send_2b: COperationNumber, 
		val_to_be_sent_2b: CValToBeSent2b
	)

	predicate CAcceptorIsValid(s: CAcceptor) 
	{
		CAcceptorIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CBallotIsValid(s.max_bal) 
		&& 
		CVotesIsValid(s.votes) 
		&& 
		(forall i :: i in s.last_checkpointed_operation ==> COperationNumberIsValid(i)) 
		&& 
		COperationNumberIsValid(s.log_truncation_point) 
		&& 
		OutboundPacketsIsValid(s.received_1b_packets) 
		&& 
		CReceived2avsIsValid(s.received_2avs) 
		&& 
		COperationNumberIsValid(s.opn_to_be_send_2b) 
		&& 
		CValToBeSent2bIsValid(s.val_to_be_sent_2b)
	}

	predicate CAcceptorIsAbstractable(s: CAcceptor) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CBallotIsAbstractable(s.max_bal) 
		&& 
		CVotesIsAbstractable(s.votes) 
		&& 
		(forall i :: i in s.last_checkpointed_operation ==> COperationNumberIsAbstractable(i)) 
		&& 
		COperationNumberIsAbstractable(s.log_truncation_point) 
		&& 
		OutboundPacketsIsAbstractable(s.received_1b_packets) 
		&& 
		CReceived2avsIsAbstractable(s.received_2avs) 
		&& 
		COperationNumberIsAbstractable(s.opn_to_be_send_2b) 
		&& 
		CValToBeSent2bIsAbstractable(s.val_to_be_sent_2b)
	}

	function AbstractifyCAcceptorToLAcceptor(s: CAcceptor) : LAcceptor 
		requires CAcceptorIsAbstractable(s)
	{
		LAcceptor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_bal), AbstractifyCVotesToVotes(s.votes), AbstractifySeq(s.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCOperationNumberToOperationNumber(s.log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(s.received_1b_packets), AbstractifyCReceived2avsToReceived2avs(s.received_2avs), AbstractifyCOperationNumberToOperationNumber(s.opn_to_be_send_2b), AbstractifyCValToBeSent2bToValToBeSent2b(s.val_to_be_sent_2b))
	}

	function method CCountMatchedValInReceived2avs(s: OutboundPackets, v: CRequestBatch) : int 
		requires OutboundPacketsIsValid(s)
		requires CRequestBatchIsValid(v)
		requires (forall p :: p in s ==> p.msg.CMessage_2av?)
		ensures var lr := CountMatchedValInReceived2avs(AbstractifyOutboundCPacketsToSeqOfRslPackets(s), AbstractifyCRequestBatchToRequestBatch(v)); var cr := CCountMatchedValInReceived2avs(s, v); (cr) == (lr)
	{
		if |s| == 0 then 
			0 
		else 
			CCountMatchedValInReceived2avs(s[ .. |s| - 1], v) + if s[|s| - 1].msg.val_2av == v then 1 else 0
	}

	function method CCountMatchedInRequestBatches(s: seq<CRequestBatch>, v: CRequestBatch) : int 
		requires (forall i :: i in s ==> CRequestBatchIsValid(i))
		requires CRequestBatchIsValid(v)
		ensures var lr := CountMatchedInRequestBatches(AbstractifySeq(s, AbstractifyCRequestBatchToRequestBatch), AbstractifyCRequestBatchToRequestBatch(v)); var cr := CCountMatchedInRequestBatches(s, v); (cr) == (lr)
	{
		if |s| == 0 then 
			0 
		else 
			CCountMatchedInRequestBatches(s[ .. |s| - 1], v) + if s[|s| - 1] == v then 1 else 0
	}

	function method CHasReceivedSame2avFromByzQuorum(r2avs: CAcceptorTuple, n: int) : bool 
		requires CAcceptorTupleIsValid(r2avs)
		requires (forall p :: p in r2avs.received_2av_packets ==> p.msg.CMessage_2av?)
		ensures var lr := HasReceivedSame2avFromByzQuorum(AbstractifyCAcceptorTupleToAcceptorTuple(r2avs), n); var cr := CHasReceivedSame2avFromByzQuorum(r2avs, n); (cr) == (lr)
	{
		(exists p :: p in r2avs.received_2av_packets && CCountMatchedValInReceived2avs(r2avs.received_2av_packets, p.msg.val_2av) >= n)
	}

	function method CIsByzQuorumSendSame2av(vals: seq<CRequestBatch>, n: int) : bool 
		requires (forall i :: i in vals ==> CRequestBatchIsValid(i))
		ensures var lr := IsByzQuorumSendSame2av(AbstractifySeq(vals, AbstractifyCRequestBatchToRequestBatch), n); var cr := CIsByzQuorumSendSame2av(vals, n); (cr) == (lr)
	{
		(exists v :: v in vals && CCountMatchedInRequestBatches(vals, v) >= n)
	}

	function method CHasReceived2avOfOpn(received_2avs: CReceived2avs, opn: COperationNumber) : bool 
		requires CReceived2avsIsValid(received_2avs)
		requires COperationNumberIsValid(opn)
		ensures var lr := HasReceived2avOfOpn(AbstractifyCReceived2avsToReceived2avs(received_2avs), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CHasReceived2avOfOpn(received_2avs, opn); (cr) == (lr)
	{
		opn in received_2avs
	}

	function method CReceived2avSetCorrect(r2avs: CAcceptorTuple, bal: CBallot, opn: COperationNumber, c: CConfiguration) : bool 
		requires CAcceptorTupleIsValid(r2avs)
		requires CBallotIsValid(bal)
		requires COperationNumberIsValid(opn)
		requires CConfigurationIsValid(c)
		ensures var lr := Received2avSetCorrect(AbstractifyCAcceptorTupleToAcceptorTuple(r2avs), AbstractifyCBallotToBallot(bal), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCConfigurationToLConfiguration(c)); var cr := CReceived2avSetCorrect(r2avs, bal, opn, c); (cr) == (lr)
	{
		|r2avs.received_2av_packets| < |c.replica_ids| 
		&& 
		(forall i, j :: 0 <= i && i < |r2avs.received_2av_packets| && 0 <= j && j < |r2avs.received_2av_packets| && i != j ==> r2avs.received_2av_packets[i] != r2avs.received_2av_packets[j] && r2avs.received_2av_packets[i].src != r2avs.received_2av_packets[j].src) 
		&& 
		(forall p :: p in r2avs.received_2av_packets ==> p.msg.CMessage_2av? && p.msg.opn_2av == opn && p.msg.bal_2av == bal && p.src in c.replica_ids)
	}

	function method CAcceptorStateCorrect(r2avs: CReceived2avs, bal: CBallot, c: CConfiguration) : bool 
		requires CReceived2avsIsValid(r2avs)
		requires CBallotIsValid(bal)
		requires CConfigurationIsValid(c)
		ensures var lr := AcceptorStateCorrect(AbstractifyCReceived2avsToReceived2avs(r2avs), AbstractifyCBallotToBallot(bal), AbstractifyCConfigurationToLConfiguration(c)); var cr := CAcceptorStateCorrect(r2avs, bal, c); (cr) == (lr)
	{
		(forall opn :: opn in r2avs ==> CReceived2avSetCorrect(r2avs[opn], bal, opn, c))
	}

	function method CIsLogTruncationPointValid(log_truncation_point: COperationNumber, last_checkpointed_operation: seq<COperationNumber>, config: CConfiguration) : bool 
		requires COperationNumberIsValid(log_truncation_point)
		requires (forall i :: i in last_checkpointed_operation ==> COperationNumberIsValid(i))
		requires CConfigurationIsValid(config)
		ensures var lr := IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCConfigurationToLConfiguration(config)); var cr := CIsLogTruncationPointValid(log_truncation_point, last_checkpointed_operation, config); (cr) == (lr)
	{
		CIsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, CByzQuorumSize(config))
	}

	function method CRemoveVotesBeforeLogTruncationPoint(votes: CVotes, log_truncation_point: COperationNumber) : CVotes 
		requires CVotesIsValid(votes)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var votes' := CRemoveVotesBeforeLogTruncationPoint(votes, log_truncation_point); CVotesIsValid(votes') && RemoveVotesBeforeLogTruncationPoint(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	{
		var t1 := 
			(map opn | opn in votes && opn >= log_truncation_point :: votes[opn]); 		
		t1
	}

	function method CAddVoteAndRemoveOldOnes(votes: CVotes, new_opn: COperationNumber, new_vote: CVote, log_truncation_point: COperationNumber) : CVotes 
		requires CVotesIsValid(votes)
		requires COperationNumberIsValid(new_opn)
		requires CVoteIsValid(new_vote)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var votes' := CAddVoteAndRemoveOldOnes(votes, new_opn, new_vote, log_truncation_point); CVotesIsValid(votes') && LAddVoteAndRemoveOldOnes(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(new_opn), AbstractifyCVoteToVote(new_vote), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	{
		var t1 := 
			(map opn | opn in votes.Keys + {new_opn} && opn >= log_truncation_point :: if opn == new_opn then new_vote else votes[opn]); 		
		t1
	}

	function method CAcceptorInit(c: CReplicaConstants) : CAcceptor 
		requires CReplicaConstantsIsValid(c)
		ensures var a := CAcceptorInit(c); CAcceptorIsValid(a) && LAcceptorInit(AbstractifyCAcceptorToLAcceptor(a), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			CBallot(0, 0); 		
		var t3 := 
			map[]; 		
		var t4 := 
			seq(|c.all.config.replica_ids|, (idx) => 0); 		
		var t5 := 
			0; 		
		var t6 := 
			map[]; 		
		var t7 := 
			[]; 		
		var t8 := 
			0; 		
		var t9 := 
			CValToBeSent2bUnknown(); 		
		CAcceptor(t1, t2, t3, t4, t5, t7, t6, t8, t9)
	}

	function method CAcceptorMaybeEnterNewView(s: CAcceptor) : CAcceptor 
		requires CAcceptorIsValid(s)
		ensures var s' := CAcceptorMaybeEnterNewView(s); CAcceptorIsValid(s') && LAcceptorMaybeEnterNewView(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'))
	{
		var t1 := 
			s.(received_1b_packets := []); 		
		t1
	}

	function method CAcceptorProcess1a(s: CAcceptor, inp: CPacket) : (CAcceptor, OutboundPackets) 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_1a?
		ensures var (s', sent_packets) := CAcceptorProcess1a(s, inp); CAcceptorIsValid(s') && OutboundPacketsIsValid(sent_packets) && LAcceptorProcess1a(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			var m := 
				inp.msg; 			
			var t1 := 
				if inp.src in s.constants.all.config.replica_ids && CBalLt(s.max_bal, m.bal_1a) && CReplicaConstantsValid(s.constants) then 
					var t1 := 
						BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1b(m.bal_1a, s.log_truncation_point, s.votes)); 					
					var t2 := 
						s.(max_bal := m.bal_1a); 					
					(t2, t1) 
				else 
					var t1 := 
						s; 					
					var t2 := 
						[]; 					
					(t1, t2); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CAcceptorProcess1b(s: CAcceptor, p: CPacket) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_1b?
		requires p.src in s.constants.all.config.replica_ids
		requires (forall other_packet :: other_packet in s.received_1b_packets ==> other_packet.src != p.src)
		ensures var s' := CAcceptorProcess1b(s, p); CAcceptorIsValid(s') && LAcceptorProcess1b(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(p))
	{
		var t1 := 
			s.(received_1b_packets := s.received_1b_packets + [p]); 		
		t1
	}

	function method CAcceptorProcess1c(s: CAcceptor, inp: CPacket) : (CAcceptor, OutboundPackets) 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_1c?
		requires inp.src in s.constants.all.config.replica_ids
		requires CBalLeq(s.max_bal, inp.msg.bal_1c)
		requires CLeqUpperBound(inp.msg.opn_1c, s.constants.all.params.max_integer_val)
		ensures var (s', sent_packets) := CAcceptorProcess1c(s, inp); CAcceptorIsValid(s') && OutboundPacketsIsValid(sent_packets) && LAcceptorProcess1c(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			var m := 
				inp.msg; 			
			var t1 := 
				var newLogTruncationPoint := 
					if inp.msg.opn_1c - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then 
						inp.msg.opn_1c - s.constants.all.params.max_log_length + 1 
					else 
						s.log_truncation_point; 				
				var t1 := 
					BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2av(m.bal_1c, m.opn_1c, m.val_1c)); 				
				var t2 := 
					if s.log_truncation_point <= inp.msg.opn_1c then 
						var t1 := 
							CAddVoteAndRemoveOldOnes(s.votes, m.opn_1c, CVote(m.bal_1c, m.val_1c), newLogTruncationPoint); 						
						t1 
					else 
						var t1 := 
							s.votes; 						
						t1; 				
				var t3 := 
					s.(max_bal := m.bal_1c, log_truncation_point := newLogTruncationPoint, votes := t2); 				
				(t3, t1); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CAcceptorProcess2av(s: CAcceptor, inp: CPacket) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_2av?
		ensures var s' := CAcceptorProcess2av(s, inp); CAcceptorIsValid(s') && LAcceptorProcess2av(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		var t1 := 
			var m := 
				inp.msg; 			
			var t1 := 
				var opn := 
					m.opn_2av; 				
				var t1 := 
					if (inp.src !in s.constants.all.config.replica_ids) || (CBalLt(m.bal_2av, s.max_bal)) then 
						var t1 := 
							s; 						
						t1 
					else 
						var t1 := 
							if CBalLt(s.max_bal, m.bal_2av) then 
								var t1 := 
									var tup' := 
										CAcceptorTuple([inp]); 									
									var t1 := 
										s.(max_bal := m.bal_2av, received_2avs := map[opn := tup']); 									
									t1; 								
								t1 
							else 
								var t1 := 
									if opn !in s.received_2avs then 
										var t1 := 
											var tup' := 
												CAcceptorTuple([inp]); 											
											var t1 := 
												s.(received_2avs := s.received_2avs[opn := tup']); 											
											t1; 										
										t1 
									else 
										var t1 := 
											if (exists p :: p in s.received_2avs[opn].received_2av_packets && p.src == inp.src) then 
												var t1 := 
													s; 												
												t1 
											else 
												var t1 := 
													var tup := 
														s.received_2avs[opn]; 													
													var t1 := 
														var tup' := 
															tup.(received_2av_packets := tup.received_2av_packets + [inp]); 														
														var t1 := 
															s.(received_2avs := s.received_2avs[opn := tup']); 														
														t1; 													
													t1; 												
												t1; 										
										t1; 								
								t1; 						
						t1; 				
				t1; 			
			t1; 		
		t1
	}

	function method CAcceptorDecide2bVal(s: CAcceptor, bal: CBallot, opn: COperationNumber, v: CRequestBatch) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires CBallotIsValid(bal)
		requires COperationNumberIsValid(opn)
		requires CRequestBatchIsValid(v)
		requires s.opn_to_be_send_2b in s.received_2avs
		requires opn == s.opn_to_be_send_2b
		requires s.val_to_be_sent_2b.CValToBeSent2bUnknown?
		ensures var s' := CAcceptorDecide2bVal(s, bal, opn, v); CAcceptorIsValid(s') && LAcceptorDecide2bVal(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCBallotToBallot(bal), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCRequestBatchToRequestBatch(v))
	{
		var t1 := 
			s.(val_to_be_sent_2b := CValToBeSent2bKnown(v, bal)); 		
		t1
	}

	function method CAcceptorSent2b(s: CAcceptor) : (CAcceptor, OutboundPackets) 
		requires CAcceptorIsValid(s)
		requires s.val_to_be_sent_2b.CValToBeSent2bKnown?
		requires s.val_to_be_sent_2b.bal == s.max_bal
		ensures var (s', sent_packets) := CAcceptorSent2b(s); CAcceptorIsValid(s') && OutboundPacketsIsValid(sent_packets) && LAcceptorSent2b(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			var opn := 
				s.opn_to_be_send_2b; 			
			var t1 := 
				var v := 
					s.val_to_be_sent_2b.v; 				
				var t1 := 
					var bal := 
						s.val_to_be_sent_2b.bal; 					
					var t1 := 
						var newLogTruncationPoint := 
							if opn - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then 
								opn - s.constants.all.params.max_log_length + 1 
							else 
								s.log_truncation_point; 						
						var t1 := 
							BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2b(bal, opn, v)); 						
						var t2 := 
							if s.log_truncation_point <= opn then 
								var t1 := 
									CAddVoteAndRemoveOldOnes(s.votes, opn, CVote(bal, v), newLogTruncationPoint); 								
								var t2 := 
									newLogTruncationPoint; 								
								(t1, t2) 
							else 
								var t1 := 
									s.votes; 								
								var t2 := 
									s.log_truncation_point; 								
								(t1, t2); 						
						var t3 := 
							s.(opn_to_be_send_2b := s.opn_to_be_send_2b + 1, val_to_be_sent_2b := CValToBeSent2bUnknown(), votes := t2.1, log_truncation_point := t2.0); 						
						(t3, t1); 					
					(t1.1, t1.0); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CAcceptorForgetReceived2avs(s: CAcceptor, opn: COperationNumber) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CAcceptorForgetReceived2avs(s, opn); CAcceptorIsValid(s') && LAcceptorForgetReceived2avs(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		var t1 := 
			if opn in s.received_2avs then 
				var t1 := 
					s.(received_2avs := CRemoveElt(s.received_2avs, opn)); 				
				t1 
			else 
				var t1 := 
					s; 				
				t1; 		
		t1
	}

	function method CAcceptorProcessHeartbeat(s: CAcceptor, inp: CPacket) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Heartbeat?
		ensures var s' := CAcceptorProcessHeartbeat(s, inp); CAcceptorIsValid(s') && LAcceptorProcessHeartbeat(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		var t1 := 
			if inp.src in s.constants.all.config.replica_ids then 
				var t1 := 
					var sender_index := 
						CGetReplicaIndex(inp.src, s.constants.all.config); 					
					var t1 := 
						if 0 <= sender_index && sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then 
							var t1 := 
								s.(last_checkpointed_operation := s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt]); 							
							t1 
						else 
							var t1 := 
								s; 							
							t1; 					
					t1; 				
				t1 
			else 
				var t1 := 
					s; 				
				t1; 		
		t1
	}

	function method CAcceptorTruncateLog(s: CAcceptor, opn: COperationNumber) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CAcceptorTruncateLog(s, opn); CAcceptorIsValid(s') && LAcceptorTruncateLog(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		var t1 := 
			if opn <= s.log_truncation_point then 
				var t1 := 
					s; 				
				t1 
			else 
				var t1 := 
					CRemoveVotesBeforeLogTruncationPoint(s.votes, opn); 				
				var t2 := 
					s.(log_truncation_point := opn, votes := t1); 				
				t2; 		
		t1
	}
}
