include ""


module Impl_LiveRSL__Learner_i 
{

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

	function method CLearnerInit(c: CReplicaConstants) : CLearner 
		requires CReplicaConstantsIsValid(c)
		ensures var l := CLearnerInit(c); CLearnerIsValid(l) && LLearnerInit(AbstractifyCLearnerToLLearner(l), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := c; 		
		var t2 := CBallot(0, 0); 		
		var t3 := map[]; 		
		CLearner(t1, t2, t3)
	}

	function method CLearnerProcess2b(s: CLearner, packet: CPacket) : CLearner 
		requires CLearnerIsValid(s)
		requires CPacketIsValid(packet)
		requires packet.msg.CMessage_2b?
		ensures var s' := CLearnerProcess2b(s, packet); CLearnerIsValid(s') && LLearnerProcess2b(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCPacketToRslPacket(packet))
	{
		var t1 := var m := packet.msg; var t1 := var opn := m.opn_2b; var t1 := if packet.src !in s.constants.all.config.replica_ids || CBalLt(m.bal_2b, s.max_ballot_seen) then var t1 := s; t1 else var t1 := if CBalLt(s.max_ballot_seen, m.bal_2b) then var t1 := var tup' := CearnerTuple({packet.src}, m.val_2b); var t1 := s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := map[opn: tup']); t1; t1 else var t1 := if opn !in s.unexecuted_learner_state then var t1 := var tup' := CearnerTuple({packet.src}, m.val_2b); var t1 := s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']); t1; t1 else var t1 := if packet.src in s.unexecuted_learner_state[opn].received_2b_message_senders then var t1 := s; t1 else var t1 := var tup := s.unexecuted_learner_state[opn]; var t1 := var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src}); var t1 := s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']); t1; t1; t1; t1; t1; t1; t1; t1; 		
		t1
	}

	function method CLearnerForgetDecision(s: CLearner, opn: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CLearnerForgetDecision(s, opn); CLearnerIsValid(s') && LLearnerForgetDecision(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		var t1 := if opn in s.unexecuted_learner_state then var t1 := s.(unexecuted_learner_state := CRemoveElt(s.unexecuted_learner_state, opn)); t1 else var t1 := s; t1; 		
		t1
	}

	function method CLearnerForgetOperationsBefore(s: CLearner, ops_complete: COperationNumber) : CLearner 
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(ops_complete)
		ensures var s' := CLearnerForgetOperationsBefore(s, ops_complete); CLearnerIsValid(s') && LLearnerForgetOperationsBefore(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(ops_complete))
	{
		var t1 := s.(unexecuted_learner_state := [Printer for ... hasn't been implemented.]); 		
		t1
	}
}
