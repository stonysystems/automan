include "../../Protocol/RSL/Acceptor.i.dfy"
include "Broadcast.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"

module LiveRSL__AcceptorModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveRSL__Acceptor_i
  import opened LiveRSL__CMessage_i
  import opened LiveRSL__CMessageRefinements_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__CPaxosConfiguration_i
  import opened LiveRSL__CTypes_i
  import opened LiveRSL__Environment_i
  import opened LiveRSL__Message_i
  import opened LiveRSL__PacketParsing_i
  import opened LiveRSL__ParametersState_i
  import opened LiveRSL__ConstantsState_i
  import opened LiveRSL__Types_i
  import opened Impl__LiveRSL__Broadcast_i
  import opened Collections__Maps_i
  import opened Collections__Maps2_s
  import opened Collections__Sets_i
  import opened Common__NodeIdentity_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened Common__UdpClient_i
  import opened Environment_s
  import opened Collections__CountMatches_i
  import opened GenericRefinement_i

  /************************** AutoMan Translation ************************/

  /** 8 + 0 */
  datatype CAcceptor = 
	CAcceptor(
		constants: CReplicaConstants, 
		max_bal: CBallot, 
		votes: CVotes, 
		last_checkpointed_operation: seq<COperationNumber>, 
		log_truncation_point: COperationNumber
	)

  /** 0 + 15 + 1 */
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
    && /* Manually added */
    |s.last_checkpointed_operation| == |s.constants.all.config.replica_ids|
	}

  /** 0 + 12 */
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

  /** 0 + 4 */
  function AbstractifyCAcceptorToLAcceptor(s: CAcceptor) : LAcceptor 
		requires CAcceptorIsAbstractable(s)
	{
		LAcceptor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_bal), AbstractifyCVotesToVotes(s.votes), AbstractifySeq(s.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCOperationNumberToOperationNumber(s.log_truncation_point))
	}

  /** 4 + 4 + 1 */
  function method CIsLogTruncationPointValid(log_truncation_point: COperationNumber, last_checkpointed_operation: seq<COperationNumber>, config: CConfiguration) : bool 
		requires COperationNumberIsValid(log_truncation_point)
		requires (forall i :: i in last_checkpointed_operation ==> COperationNumberIsValid(i))
		requires CConfigurationIsValid(config)
		ensures CIsLogTruncationPointValid(log_truncation_point, last_checkpointed_operation, config) == IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCConfigurationToLConfiguration(config))
	{
    /* manually add */
    assert AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber) == last_checkpointed_operation;
		IsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, CMinQuorumSize(config))
	}

  /** 5 + 3 + 2 */
  function method CRemoveVotesBeforeLogTruncationPoint(votes: CVotes, log_truncation_point: COperationNumber) : CVotes 
		requires CVotesIsValid(votes)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var votes' := CRemoveVotesBeforeLogTruncationPoint(votes, log_truncation_point); CVotesIsValid(votes') && RemoveVotesBeforeLogTruncationPoint(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	{
    var t1 := (map opn | opn in votes && opn >= log_truncation_point :: votes[opn]); 	
    lemma_voteLen(t1);	
		t1
	}

  /** 5 + 5 + 1 */
	function method CAddVoteAndRemoveOldOnes(votes: CVotes, new_opn: COperationNumber, new_vote: CVote, log_truncation_point: COperationNumber) : CVotes 
		requires CVotesIsValid(votes)
		requires COperationNumberIsValid(new_opn)
		requires CVoteIsValid(new_vote)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var votes' := CAddVoteAndRemoveOldOnes(votes, new_opn, new_vote, log_truncation_point); CVotesIsValid(votes') && LAddVoteAndRemoveOldOnes(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(new_opn), AbstractifyCVoteToVote(new_vote), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	{
		var t1 := (map opn | opn in votes.Keys + {new_opn} && opn >= log_truncation_point :: if opn == new_opn then new_vote else votes[opn]); 		
    lemma_voteLen(t1);
		t1
	}

  /** 9 + 2 */
  function method CAcceptorInit(c: CReplicaConstants) : CAcceptor 
		requires CReplicaConstantsIsValid(c)
		ensures var a := CAcceptorInit(c); CAcceptorIsValid(a) && LAcceptorInit(AbstractifyCAcceptorToLAcceptor(a), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := c; 		
		var t2 := CBallot(0, 0); 		
		var t3 := map[]; 		
		var t4 := seq(|c.all.config.replica_ids|, (idx) => 0); 		
		var t5 := 0; 		
		CAcceptor(t1, t2, t3, t4, t5)
	}

  /** 18 + 4 */
  function method CAcceptorProcess1a(s: CAcceptor, inp: CPacket) : (CAcceptor, OutboundPackets) 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_1a?
		ensures var (s', broadcast_sent_packets) := CAcceptorProcess1a(s, inp); CAcceptorIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LAcceptorProcess1a(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := var m := inp.msg; 
      var t1 := 
        if inp.src in s.constants.all.config.replica_ids && CBalLt(s.max_bal, m.bal_1a) /*&& CReplicaConstantsValid(s.constants)*/ then 
          var t1 := 
            PacketSequence(
            [CPacket(inp.src, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_1b(m.bal_1a, s.log_truncation_point, s.votes))]
            ); 
          var t2 := s.(max_bal := m.bal_1a); 
          (t2, t1) 
        else 
          var t1 := s; 
          var t2 := PacketSequence([]); 
          (t1, t2); 
        (t1.1, t1.0); 		
		(t1.1, t1.0)
	}

  /** 22 + 7 */
	function method CAcceptorProcess2a(s: CAcceptor, inp: CPacket) : (CAcceptor, OutboundPackets) 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_2a?
		requires inp.src in s.constants.all.config.replica_ids
		requires CBalLeq(s.max_bal, inp.msg.bal_2a)
		requires CLeqUpperBound(inp.msg.opn_2a, s.constants.all.params.max_integer_val)
		ensures var (s', broadcast_sent_packets) := CAcceptorProcess2a(s, inp); CAcceptorIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LAcceptorProcess2a(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := var m := inp.msg; 
    var t1 := var newLogTruncationPoint := 
      if inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then 
        inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 
      else 
        s.log_truncation_point; 
    var t1 := Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2b(m.bal_2a, m.opn_2a, m.val_2a))); 
    var t2 := m.bal_2a; 
    var t3 := newLogTruncationPoint; 
    var t4 := 
      if s.log_truncation_point <= inp.msg.opn_2a then 
        var t1 := CAddVoteAndRemoveOldOnes(s.votes, m.opn_2a, CVote(m.bal_2a, m.val_2a), newLogTruncationPoint); 
        t1 
      else 
        var t1 := s.votes; 
        t1; 
      var t5 := s.constants; 
      var t6 := s.last_checkpointed_operation; 
      (CAcceptor(t5, t2, t4, t6, t3), t1); (t1.1, t1.0); 		
		(t1.1, t1.0)
	}

  /** 22 + 4 */
  function method CAcceptorProcessHeartbeat(s: CAcceptor, inp: CPacket) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Heartbeat?
		ensures var s' := CAcceptorProcessHeartbeat(s, inp); CAcceptorIsValid(s') && LAcceptorProcessHeartbeat(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		var t1 := 
      if inp.src in s.constants.all.config.replica_ids then 
        var t1 := 
        var sender_index := CGetReplicaIndex(inp.src, s.constants.all.config); 
        var t1 := 
          if 0 <= sender_index && sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then 
            var t1 := s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt]; 
            var t2 := s.constants; 
            var t3 := s.max_bal; 
            var t4 := s.votes; 
            var t5 := s.log_truncation_point; 
            CAcceptor(t2, t3, t4, t1, t5) 
          else 
            var t1 := s; 
            t1; 
          t1; 
        t1 
      else 
        var t1 := s; 
        t1; 		
		t1
	}

  /** 15 + 3 */
  function method CAcceptorTruncateLog(s: CAcceptor, opn: COperationNumber) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CAcceptorTruncateLog(s, opn); CAcceptorIsValid(s') && LAcceptorTruncateLog(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{ 
    var t1 := 
      if opn <= s.log_truncation_point then 
        var t1 := s; 
        t1 
      else 
        var t1 := 
        var a := s.log_truncation_point; 
        var t1 := CRemoveVotesBeforeLogTruncationPoint(s.votes, opn); 
        var t2 := s.(log_truncation_point := opn, votes := t1); 
        t2; 
      t1;  		
		t1
	}

  /************************** AutoMan Translation End ********************/ 

  lemma {:axiom} lemma_voteLen(votes:CVotes)
    ensures |votes| < max_votes_len()

}
