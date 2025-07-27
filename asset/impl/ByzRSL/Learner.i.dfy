/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__Learner_i

[Action] LLearnerInit
Check passed

[Action] LLearnerProcess2b
Check passed

[Action] LLearnerForgetDecision
Check passed

[Action] LLearnerForgetOperationsBefore
Check passed
**********************************************************************/

include ""


module Impl_LiveByzRSL__Learner_i 
{

	datatype CearnerTuple = 
	CearnerTuple(
		received_2bs: OutboundPackets
	)

	predicate CearnerTupleIsValid(s: CearnerTuple) 
	{
		CearnerTupleIsAbstractable(s) 
		&& 
		OutboundPacketsIsValid(s.received_2bs)
	}

	predicate CearnerTupleIsAbstractable(s: CearnerTuple) 
	{
		OutboundPacketsIsAbstractable(s.received_2bs)
	}

	function AbstractifyCearnerTupleToLearnerTuple(s: CearnerTuple) : LearnerTuple 
		requires CearnerTupleIsAbstractable(s)
	{
		LearnerTuple(AbstractifyOutboundCPacketsToSeqOfRslPackets(s.received_2bs))
	}
	type CearnerState = map<COperationNumber, CearnerTuple>

	predicate CearnerStateIsAbstractable(s: CearnerState) 
	{
		(forall i :: i in s ==> COperationNumberIsAbstractable(i) && CearnerTupleIsAbstractable(s[i]))
	}

	predicate CearnerStateIsValid(s: CearnerState) 
	{
		CearnerStateIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CearnerTupleIsValid(s[i]))
	}

	function AbstractifyCearnerStateToLearnerState(s: CearnerState) : LearnerState 
		requires CearnerStateIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyCOperationNumberToOperationNumber, AbstractifyLearnerTupleToCearnerTuple, AbstractifyOperationNumberToCOperationNumber)
	}

	datatype CLearner = 
	CLearner(
		constants: CReplicaConstants, 
		max_ballot_seen: CBallot, 
		unexecuted_learner_state: CearnerState
	)

	predicate CLearnerIsValid(s: CLearner) 
	{
		CLearnerIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CBallotIsValid(s.max_ballot_seen) 
		&& 
		CearnerStateIsValid(s.unexecuted_learner_state)
	}

	predicate CLearnerIsAbstractable(s: CLearner) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CBallotIsAbstractable(s.max_ballot_seen) 
		&& 
		CearnerStateIsAbstractable(s.unexecuted_learner_state)
	}

	function AbstractifyCLearnerToLLearner(s: CLearner) : LLearner 
		requires CLearnerIsAbstractable(s)
	{
		LLearner(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_ballot_seen), AbstractifyCearnerStateToLearnerState(s.unexecuted_learner_state))
	}

	function method CCountMatchedValInReceived2bs(s: OutboundPackets, v: CRequestBatch) : int 
		requires OutboundPacketsIsValid(s)
		requires CRequestBatchIsValid(v)
		requires (forall p :: p in s ==> p.msg.CMessage_2b?)
		ensures var lr := CountMatchedValInReceived2bs(AbstractifyOutboundCPacketsToSeqOfRslPackets(s), AbstractifyCRequestBatchToRequestBatch(v)); var cr := CCountMatchedValInReceived2bs(s, v); (cr) == (lr)
	{
		if |s| == 0 then 
			0 
		else 
			CCountMatchedValInReceived2bs(s[ .. |s| - 1], v) + if s[|s| - 1].msg.val_2b == v then 1 else 0
	}

	function method CIsWeakQuorumSendSame2b(vals: seq<CRequestBatch>, n: int) : bool 
		requires (forall i :: i in vals ==> CRequestBatchIsValid(i))
		ensures var lr := IsWeakQuorumSendSame2b(AbstractifySeq(vals, AbstractifyCRequestBatchToRequestBatch), n); var cr := CIsWeakQuorumSendSame2b(vals, n); (cr) == (lr)
	{
		(exists v :: v in vals && CCountMatchedInRequestBatches(vals, v) >= n)
	}

	function method CHasReceivedSame2bFromWeakQuorum(tup: CearnerTuple, n: int) : bool 
		requires CearnerTupleIsValid(tup)
		requires (forall p :: p in tup.received_2bs ==> p.msg.CMessage_2b?)
		ensures var lr := HasReceivedSame2bFromWeakQuorum(AbstractifyCearnerTupleToLearnerTuple(tup), n); var cr := CHasReceivedSame2bFromWeakQuorum(tup, n); (cr) == (lr)
	{
		(exists p :: p in tup.received_2bs && CCountMatchedValInReceived2bs(tup.received_2bs, p.msg.val_2b) >= n)
	}

	function method CearnerTupleCorrect(tup: CearnerTuple, bal: CBallot, opn: COperationNumber, c: CConfiguration) : bool 
		requires CearnerTupleIsValid(tup)
		requires CBallotIsValid(bal)
		requires COperationNumberIsValid(opn)
		requires CConfigurationIsValid(c)
		ensures var lr := LearnerTupleCorrect(AbstractifyCearnerTupleToLearnerTuple(tup), AbstractifyCBallotToBallot(bal), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCConfigurationToLConfiguration(c)); var cr := CearnerTupleCorrect(tup, bal, opn, c); (cr) == (lr)
	{
		|tup.received_2bs| < |c.replica_ids| 
		&& 
		(forall i, j :: 0 <= i && i < |tup.received_2bs| && 0 <= j && j < |tup.received_2bs| && i != j ==> tup.received_2bs[i] != tup.received_2bs[j] && tup.received_2bs[i].src != tup.received_2bs[j].src) 
		&& 
		(forall p :: p in tup.received_2bs ==> p.msg.CMessage_2b? && p.msg.opn_2b == opn && p.msg.bal_2b == bal && p.src in c.replica_ids)
	}

	function method CearnerStateCorrect(ls: CearnerState, bal: CBallot, c: CConfiguration) : bool 
		requires CearnerStateIsValid(ls)
		requires CBallotIsValid(bal)
		requires CConfigurationIsValid(c)
		ensures var lr := LearnerStateCorrect(AbstractifyCearnerStateToLearnerState(ls), AbstractifyCBallotToBallot(bal), AbstractifyCConfigurationToLConfiguration(c)); var cr := CearnerStateCorrect(ls, bal, c); (cr) == (lr)
	{
		(forall opn :: opn in ls ==> CearnerTupleCorrect(ls[opn], bal, opn, c))
	}

	function method CLearnerInit(c: CReplicaConstants) : CLearner 
		requires CReplicaConstantsIsValid(c)
		ensures var l := CLearnerInit(c); CLearnerIsValid(l) && LLearnerInit(AbstractifyCLearnerToLLearner(l), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			CBallot(0, 0); 		
		var t3 := 
			map[]; 		
		CLearner(t1, t2, t3)
	}

	function method CLearnerProcess2b(s: CLearner, packet: CPacket) : CLearner 
		requires CLearnerIsValid(s)
		requires CPacketIsValid(packet)
		requires packet.msg.CMessage_2b?
		requires CearnerStateCorrect(s.unexecuted_learner_state, s.max_ballot_seen, s.constants.all.config)
		ensures var s' := CLearnerProcess2b(s, packet); CLearnerIsValid(s') && LLearnerProcess2b(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCPacketToRslPacket(packet))
	{
		var t1 := 
			var m := 
				packet.msg; 			
			var t1 := 
				var opn := 
					m.opn_2b; 				
				var t1 := 
					if (packet.src !in s.constants.all.config.replica_ids) || (CBalLt(m.bal_2b, s.max_ballot_seen)) then 
						var t1 := 
							s; 						
						t1 
					else 
						var t1 := 
							if CBalLt(s.max_ballot_seen, m.bal_2b) then 
								var t1 := 
									var tup' := 
										CearnerTuple([packet]); 									
									var t1 := 
										s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := map[opn := tup']); 									
									t1; 								
								t1 
							else 
								var t1 := 
									if opn !in s.unexecuted_learner_state then 
										var t1 := 
											var tup' := 
												CearnerTuple([packet]); 											
											var t1 := 
												s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']); 											
											t1; 										
										t1 
									else 
										var t1 := 
											if (exists p :: p in s.unexecuted_learner_state[opn].received_2bs && p.src == packet.src) then 
												var t1 := 
													s; 												
												t1 
											else 
												var t1 := 
													var tup := 
														s.unexecuted_learner_state[opn]; 													
													var t1 := 
														var tup' := 
															tup.(received_2bs := tup.received_2bs + [packet]); 														
														var t1 := 
															s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']); 														
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

	function method CLearnerForgetDecision(s: CLearner, opn: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CLearnerForgetDecision(s, opn); CLearnerIsValid(s') && LLearnerForgetDecision(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		var t1 := 
			if opn in s.unexecuted_learner_state then 
				var t1 := 
					s.(unexecuted_learner_state := CRemoveElt(s.unexecuted_learner_state, opn)); 				
				t1 
			else 
				var t1 := 
					s; 				
				t1; 		
		t1
	}

	function method CLearnerForgetOperationsBefore(s: CLearner, ops_complete: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(ops_complete)
		ensures var s' := CLearnerForgetOperationsBefore(s, ops_complete); CLearnerIsValid(s') && LLearnerForgetOperationsBefore(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(ops_complete))
	{
		var t1 := 
			s.(unexecuted_learner_state := (map op | op in s.unexecuted_learner_state && op >= ops_complete :: s.unexecuted_learner_state[op])); 		
		t1
	}
}
