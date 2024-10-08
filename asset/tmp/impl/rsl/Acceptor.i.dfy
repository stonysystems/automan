Parsing include file: ./asset/tmp/spec/rsl/Environment.i.dfy
Parsing include file: ./asset/tmp/spec/rsl/Types.i.dfy
Warning: Include file not found: ./asset/tmp/spec/rsl/../../Services/RSL/AppStateMachine.i.dfy
Warning: Include file not found: ./asset/tmp/spec/rsl/../Common/NodeIdentity.i.dfy
Parsing include file: ./asset/tmp/spec/rsl/Message.i.dfy
Warning: Include file not found: ./asset/tmp/spec/rsl/../../Common/Framework/Environment.s.dfy
Parsing include file: ./asset/tmp/spec/rsl/Configuration.i.dfy
Warning: Include file not found: ./asset/tmp/spec/rsl/../../Common/Collections/Sets.i.dfy
Warning: Include file not found: ./asset/tmp/spec/rsl/../../Common/Collections/Seqs.i.dfy
Parsing include file: ./asset/tmp/spec/rsl/Constants.i.dfy
Parsing include file: ./asset/tmp/spec/rsl/Parameters.i.dfy
Warning: Include file not found: ./asset/tmp/spec/rsl/../Common/UpperBound.s.dfy
Parsing include file: ./asset/tmp/spec/rsl/Broadcast.i.dfy
Warning: Include file not found: ./asset/tmp/spec/rsl/../../Common/Collections/CountMatches.i.dfy
include ""


module Impl_LiveRSL__Acceptor_i 
{

	datatype CAcceptor = 
	CAcceptor(
		constants: CReplicaConstants, 
		max_bal: CBallot, 
		votes: CVotes, 
		last_checkpointed_operation: seq<COperationNumber>, 
		log_truncation_point: COperationNumber
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
	}

	function AbstractifyCAcceptorToLAcceptor(s: CAcceptor) : LAcceptor 
		requires CAcceptorIsAbstractable(s)
	{
		LAcceptor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_bal), AbstractifyCVotesToVotes(s.votes), AbstractifySeq(s.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCOperationNumberToOperationNumber(s.log_truncation_point))
	}

	function method CAcceptorProcessHeartbeat(s: CAcceptor, inp: CPacket) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Heartbeat?
		ensures var s' := CAcceptorProcessHeartbeat(s, inp); CAcceptorIsValid(s') && LAcceptorProcessHeartbeat(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		var t1 := if inp.src in s.constants.all.config.replica_ids then var t1 := var sender_index := GetReplicaIndex(inp.src, s.constants.all.config); var t1 := if 0 <= sender_index && sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt < s.last_checkpointed_operation[sender_index] then var t1 := s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt]; var t2 := s.constants; var t3 := s.max_bal; var t4 := s.votes; var t5 := s.log_truncation_point; LAcceptor(t2, t3, t4, t1, t5) else var t1 := s; t1; t1; t1 else var t1 := s; t1; 		
		t1
	}

	function method CAcceptorTruncateLog(s: CAcceptor, opn: COperationNumber) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CAcceptorTruncateLog(s, opn); CAcceptorIsValid(s') && LAcceptorTruncateLog(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		var t1 := if opn <= s.log_truncation_point then var t1 := s; t1 else var t1 := RemoveVotesBeforeLogTruncationPoint(s.votes, opn); var t2 := s.(log_truncation_point := opn, votes := t1); t2; 		
		t1
	}
}
