include "Environment.i.dfy"
include "Configuration.i.dfy"
include "Constants.i.dfy"
include "Broadcast.i.dfy"
include "ToBeFilled.i.dfy"

module Impl_LiveRSL__Acceptor_i {
 	import opened Impl_LiveRSL__Environment_i
	import opened Impl_LiveRSL__Configuration_i
	import opened Impl_LiveRSL__Constants_i
	import opened Impl_LiveRSL__Broadcast_i
	import opened Impl_LiveRSL__Types_i
	import opened Impl_LiveRSL__Message_i
	import opened ToBeFilled
	import opened ToBeFilled
	import opened ToBeFilled

	datatype CAcceptor = 
	CAcceptor
	(
		constants : CReplicaConstants ,
		max_bal : CBallot ,
		votes : CVotes ,
		last_checkpointed_operation : seq<COperationNumber> ,
		log_truncation_point : COperationNumber
	)

	predicate CAcceptorIsValid(
		s : CAcceptor)
		
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

	predicate CAcceptorIsAbstractable(
		s : CAcceptor)
		
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

	function AbstractifyCAcceptorToLAcceptor(
		s : CAcceptor) : LAcceptor
		requires CAcceptorIsAbstractable(s)
	{
		LAcceptor(
			AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), 
			AbstractifyCBallotToBallot(s.max_bal), 
			AbstractifyCVotesToVotes(s.votes), 
			AbstractifySeq(
				s.last_checkpointed_operation, 
				AbstractifyCOperationNumberToOperationNumber), 
			AbstractifyCOperationNumberToOperationNumber(s.log_truncation_point))
	}

	function method CIsLogTruncationPointValid(
		log_truncation_point : COperationNumber ,
		last_checkpointed_operation : seq<COperationNumber> ,
		config : CConfiguration) : bool
		requires COperationNumberIsValid(log_truncation_point)
		requires (forall i :: i in last_checkpointed_operation ==> COperationNumberIsValid(i))
		requires CConfigurationIsValid(config)
		ensures 
		var bc := CIsLogTruncationPointValid(log_truncation_point, last_checkpointed_operation, config); 
		var bl := IsLogTruncationPointValid(
			AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
			AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), 
			AbstractifyCConfigurationToLConfiguration(config)); (bl) == (bc)
	{
		CIsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, CMinQuorumSize(config))
	}

	function method CRemoveVotesBeforeLogTruncationPoint(
		votes : CVotes ,
		log_truncation_point : COperationNumber) : CVotes
		requires CVotesIsValid(votes)
		requires COperationNumberIsValid(log_truncation_point)
		ensures 
			var votes' := 
				CRemoveVotesBeforeLogTruncationPoint(votes, log_truncation_point); 
			CVotesIsValid(votes') 
			&& 
			RemoveVotesBeforeLogTruncationPoint(
				AbstractifyCVotesToVotes(votes), 
				AbstractifyCVotesToVotes(votes'), 
				AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	{
		map opn | opn in votes && opn >= log_truncation_point :: votes[opn]
	}

	function method CAddVoteAndRemoveOldOnes(
		votes : CVotes ,
		new_opn : COperationNumber ,
		new_vote : CVote ,
		log_truncation_point : COperationNumber) : CVotes
		requires CVotesIsValid(votes)
		requires COperationNumberIsValid(new_opn)
		requires CVoteIsValid(new_vote)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var votes' := CAddVoteAndRemoveOldOnes(votes, new_opn, new_vote, log_truncation_point); CVotesIsValid(votes') && LAddVoteAndRemoveOldOnes(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(new_opn), AbstractifyCVoteToVote(new_vote), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	{
		map opn | opn in (votes.Keys + {new_opn}) && opn >= log_truncation_point :: (if opn == new_opn then new_vote else votes[opn])
	}

	function method CAcceptorInit(
		c : CReplicaConstants) : CAcceptor
		requires CReplicaConstantsIsValid(c)
		ensures var a := CAcceptorInit(c); 
		CAcceptorIsValid(a) && 
		LAcceptorInit(AbstractifyCAcceptorToLAcceptor(a), 
		AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		CAcceptor(constants := c, last_checkpointed_operation := seq(|c.all.config.replica_ids|, idx => 0), log_truncation_point := 0, max_bal := CBallot(0, 0), votes := map[])
	}

	function method CAcceptorProcess1a(
		s : CAcceptor ,
		inp : CPacket) : (CAcceptor, CBroadcast)
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_1a?
		ensures var (s', broadcast_sent_packets) := CAcceptorProcess1a(s, inp); 
		CAcceptorIsValid(s') 
		&& 
		(forall i :: i in broadcast_sent_packets ==> i.CPacket? && CPacketIsValid(i)) 
		&& 
		LAcceptorProcess1a(
			AbstractifyCAcceptorToLAcceptor(s), 
			AbstractifyCAcceptorToLAcceptor(s'), 
			AbstractifyCPacketToRslPacket(inp), 
			AbstractifyCBroadcastToRlsPacketSeq(broadcast_sent_packets))
	{
		var m := inp.msg; 
		if inp.src in s.constants.all.config.replica_ids && CBalLt(s.max_bal, m.bal_1a) && CReplicaConstantsValid(s.constants)
		then 
			(
				s.(
					max_bal := m.bal_1a
				),
				CBroadcast(s.constants.all.config.replica_ids[s.constants.my_index], [inp.src], CMessage_1b(m.bal_1a, s.log_truncation_point, s.votes))
			)
		else 
			(
				s,
				CBroadcastNop
			)
	}

	function method CAcceptorProcess2a(
		s : CAcceptor ,
		inp : CPacket) : (CAcceptor, CBroadcast)
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_2a?
		requires inp.src in s.constants.all.config.replica_ids
		requires CBalLeq(s.max_bal, inp.msg.bal_2a)
		requires CLeqUpperBound(inp.msg.opn_2a, s.constants.all.params.max_integer_val)
		ensures var (s', broadcast_sent_packets) := CAcceptorProcess2a(s, inp); 
		CAcceptorIsValid(s') 
		&& 
		(forall i :: i in broadcast_sent_packets ==> i.CPacket? && CPacketIsValid(i)) 
		&& 
		LAcceptorProcess2a(
			AbstractifyCAcceptorToLAcceptor(s), 
			AbstractifyCAcceptorToLAcceptor(s'), 
			AbstractifyCPacketToRslPacket(inp), 
			AbstractifyCBroadcastToRlsPacketSeq(broadcast_sent_packets))
	{
		var m := inp.msg; 
		var newLogTruncationPoint := if inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 else s.log_truncation_point; 
		if s.log_truncation_point <= inp.msg.opn_2a
		then 
			(
				s.(
					constants := s.constants,
					last_checkpointed_operation := s.last_checkpointed_operation,
					log_truncation_point := newLogTruncationPoint,
					max_bal := m.bal_2a,
					votes := CAddVoteAndRemoveOldOnes(s.votes, m.opn_2a, CVote(m.bal_2a, m.val_2a), newLogTruncationPoint)
				),
				BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2b(m.bal_2a, m.opn_2a, m.val_2a))
			)
		else 
			(
				s.(
					constants := s.constants,
					last_checkpointed_operation := s.last_checkpointed_operation,
					log_truncation_point := newLogTruncationPoint,
					max_bal := m.bal_2a,
					votes := s.votes
				),
				BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2b(m.bal_2a, m.opn_2a, m.val_2a))
			)
	}

	function method CAcceptorProcessHeartbeat(
		s : CAcceptor ,
		inp : CPacket) : CAcceptor
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Heartbeat?
		ensures var s' := CAcceptorProcessHeartbeat(s, inp); CAcceptorIsValid(s') && LAcceptorProcessHeartbeat(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		if inp.src in s.constants.all.config.replica_ids
		then 
			var sender_index := CGetReplicaIndex(inp.src, s.constants.all.config); 
			if 0 <= sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index]
			then 
				s.(
					constants := s.constants,
					last_checkpointed_operation := s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt],
					log_truncation_point := s.log_truncation_point,
					max_bal := s.max_bal,
					votes := s.votes
				)
			else 
				s
		else 
			s
	}

	function method CAcceptorTruncateLog(
		s : CAcceptor ,
		opn : COperationNumber) : CAcceptor
		requires CAcceptorIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CAcceptorTruncateLog(s, opn); CAcceptorIsValid(s') && LAcceptorTruncateLog(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		if opn <= s.log_truncation_point
		then 
			s
		else 
			s.(
				log_truncation_point := opn,
				votes := CRemoveVotesBeforeLogTruncationPoint(s.votes, opn)
			)
	}
 
}
