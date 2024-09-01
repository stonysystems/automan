include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "Constants.i.dfy"
include "Executor.i.dfy"
include "ToBeFilled.i.dfy"

module Impl_LiveRSL__Learner_i {
 	import opened Impl_LiveRSL__Configuration_i
	import opened Impl_LiveRSL__Environment_i
	import opened Impl_LiveRSL__Types_i
	import opened Impl_LiveRSL__Constants_i
	import opened Impl_LiveRSL__Executor_i
	import opened ToBeFilled

	datatype CLearner = 
	CLearner
	(
		constants : CReplicaConstants ,
		max_ballot_seen : CBallot ,
		unexecuted_learner_state : CLearnerState
	)

	predicate CLearnerIsValid(
		s : CLearner)
		
	{
		CLearnerIsAbstractable(s)
		&&
		CReplicaConstantsIsValid(s.constants)
		&&
		CBallotIsValid(s.max_ballot_seen)
		&&
		CLearnerStateIsValid(s.unexecuted_learner_state)
	}

	predicate CLearnerIsAbstractable(
		s : CLearner)
		
	{
		CReplicaConstantsIsAbstractable(s.constants)
		&&
		CBallotIsAbstractable(s.max_ballot_seen)
		&&
		CLearnerStateIsAbstractable(s.unexecuted_learner_state)
	}

	function AbstractifyCLearnerToLLearner(
		s : CLearner) : LLearner
		requires CLearnerIsAbstractable(s)
	{
		LLearner(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_ballot_seen), AbstractifyCLearnerStateToLearnerState(s.unexecuted_learner_state))
	}

	function method CLearnerInit(
		c : CReplicaConstants) : CLearner
		requires CReplicaConstantsIsValid(c)
		ensures var l := CLearnerInit(c); CLearnerIsValid(l) && LLearnerInit(AbstractifyCLearnerToLLearner(l), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		CLearner(constants := c, max_ballot_seen := CBallot(0, 0), unexecuted_learner_state := map[])
	}

	function method CLearnerProcess2b(
		s : CLearner ,
		packet : CPacket) : CLearner
		requires CLearnerIsValid(s)
		requires CPacketIsValid(packet)
		requires packet.msg.CMessage_2b?
		ensures var s' := CLearnerProcess2b(s, packet); CLearnerIsValid(s') && LLearnerProcess2b(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCPacketToRslPacket(packet))
	{
		var m := packet.msg; 
		var opn := m.opn_2b; 
		if packet.src !in s.constants.all.config.replica_ids || CBalLt(m.bal_2b, s.max_ballot_seen)
		then 
			s
		else 
			if CBalLt(s.max_ballot_seen, m.bal_2b)
			then 
				var tup' := CLearnerTuple({packet.src}, m.val_2b); 
				s.(
					max_ballot_seen := m.bal_2b,
					unexecuted_learner_state := map[opn := tup']
				)
			else 
				if opn !in s.unexecuted_learner_state
				then 
					var tup' := CLearnerTuple({packet.src}, m.val_2b); 
					s.(
						unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']
					)
				else 
					if packet.src in s.unexecuted_learner_state[opn].received_2b_message_senders
					then 
						s
					else 
						var tup := s.unexecuted_learner_state[opn]; 
						var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src}); 
						s.(
							unexecuted_learner_state := s.unexecuted_learner_state[opn := tup']
						)
	}

	function method CLearnerForgetDecision(
		s : CLearner ,
		opn : COperationNumber) : CLearner
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CLearnerForgetDecision(s, opn); CLearnerIsValid(s') && LLearnerForgetDecision(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		if opn in s.unexecuted_learner_state
		then 
			s.(
				unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn)
			)
		else 
			s
	}

	function method CLearnerForgetOperationsBefore(
		s : CLearner ,
		ops_complete : COperationNumber) : CLearner
		requires CLearnerIsValid(s)
		requires COperationNumberIsValid(ops_complete)
		ensures var s' := CLearnerForgetOperationsBefore(s, ops_complete); CLearnerIsValid(s') && LLearnerForgetOperationsBefore(AbstractifyCLearnerToLLearner(s), AbstractifyCLearnerToLLearner(s'), AbstractifyCOperationNumberToOperationNumber(ops_complete))
	{
		s.(
			unexecuted_learner_state := (map op | op in s.unexecuted_learner_state && op >= ops_complete :: s.unexecuted_learner_state[op])
		)
	}
 
}
