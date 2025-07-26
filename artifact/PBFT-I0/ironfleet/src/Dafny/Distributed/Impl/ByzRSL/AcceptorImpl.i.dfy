include "../../Protocol/ByzRSL/Acceptor.i.dfy"
include "Broadcast.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"

module LiveByzRSL__AcceptorModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__Acceptor_i
  import opened LiveByzRSL__CMessage_i
  // import opened LiveRSL__CMessageRefinements_i
  import opened LiveByzRSL__Configuration_i
  import opened LiveByzRSL__CConfiguration_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__Environment_i
  import opened LiveByzRSL__Message_i
  import opened LiveByzRSL__PacketParsing_i
  import opened LiveByzRSL__ParametersState_i
  import opened LiveByzRSL__ConstantsState_i
  import opened LiveByzRSL__Types_i
  import opened Impl__LiveByzRSL__Broadcast_i
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
  // import opened Collections__CountMatches_i

  /************************** AutoMan Translation ************************/

	/** 3 + 0 */
  	datatype CAcceptorTuple = 
	CAcceptorTuple(
		received_2av_packets: seq<CPacket>
	)

	/** 0 + 6 */
	predicate CAcceptorTupleIsValid(s: CAcceptorTuple) 
	{
		CAcceptorTupleIsAbstractable(s) 
		&& 
		SeqIsValid(s.received_2av_packets, CPacketIsValid)
	}

	/** 0 + 4 */
	predicate CAcceptorTupleIsAbstractable(s: CAcceptorTuple) 
	{
		SeqIsAbstractable(s.received_2av_packets, AbstractifyCPacketToRslPacket)
	}

	/** 0 + 5 */
	function AbstractifyCAcceptorTupleToAcceptorTuple(s: CAcceptorTuple) : AcceptorTuple 
		requires CAcceptorTupleIsAbstractable(s)
	{
		AcceptorTuple(AbstractifySeq(s.received_2av_packets, AbstractifyCPacketToRslPacket))
	}

	/** 1 + 0 */
  	type CReceived2avs = map<COperationNumber, CAcceptorTuple>

	/** 0 + 4 */
	predicate CReceived2avsIsAbstractable(s: CReceived2avs) 
	{
		(forall i :: i in s ==> COperationNumberIsAbstractable(i) && CAcceptorTupleIsAbstractable(s[i]))
	}

	/** 0 + 6 */
	predicate CReceived2avsIsValid(s: CReceived2avs) 
	{
		CReceived2avsIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CAcceptorTupleIsValid(s[i]))
	}

	/** 0 + 5 */
	function AbstractifyCReceived2avsToReceived2avs(s: CReceived2avs) : Received2avs 
		requires CReceived2avsIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyCOperationNumberToOperationNumber, AbstractifyCAcceptorTupleToAcceptorTuple, AbstractifyOperationNumberToCOperationNumber)
	}

	/** 7 + 0 */
  	datatype CValToBeSent2b = 
	CValToBeSent2bKnown(
		v: CRequestBatch, 
		bal: CBallot
	)
	 | 
	CValToBeSent2bUnknown(
	)

	/** 0 + 6 */
	predicate CValToBeSent2bIsValid(s: CValToBeSent2b) 
	{
		match s
		case CValToBeSent2bKnown(v, bal) => CValToBeSent2bIsAbstractable(s) && CRequestBatchIsValid(s.v) && CBallotIsValid(s.bal)
		case CValToBeSent2bUnknown() => CValToBeSent2bIsAbstractable(s)
	}

	/** 0 + 6 */
	predicate CValToBeSent2bIsAbstractable(s: CValToBeSent2b) 
	{
		match s
		case CValToBeSent2bKnown(v, bal) => CRequestBatchIsAbstractable(s.v) && CBallotIsAbstractable(s.bal)
		case CValToBeSent2bUnknown() => true
	}

	/** 0 + 6 */
	function AbstractifyCValToBeSent2bToValToBeSent2b(s: CValToBeSent2b) : ValToBeSent2b 
		requires CValToBeSent2bIsAbstractable(s)
	{
		match s
		case CValToBeSent2bKnown(v, bal) => ValToBeSent2bKnown(AbstractifyCRequestBatchToRequestBatch(s.v), AbstractifyCBallotToBallot(s.bal))
		case CValToBeSent2bUnknown() => ValToBeSent2bUnknown()
	}

  /** 11 + 0 */
  datatype CAcceptor = 
	CAcceptor(
		constants: CReplicaConstants, 
		max_bal: CBallot, 
		votes: CVotes, 
		last_checkpointed_operation: seq<COperationNumber>, 
		log_truncation_point: COperationNumber, 
		received_1b_packets: seq<CPacket>, 
		received_2avs: CReceived2avs, 
		opn_to_be_send_2b: COperationNumber, 
		val_to_be_sent_2b: CValToBeSent2b
	)

  /** 0 + 23 + 1 */
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
		SeqIsValid(s.received_1b_packets, CPacketIsValid) 
		&& 
		CReceived2avsIsValid(s.received_2avs) 
		&& 
		COperationNumberIsValid(s.opn_to_be_send_2b) 
		&& 
		CValToBeSent2bIsValid(s.val_to_be_sent_2b)
    && /* Manually added */
    |s.last_checkpointed_operation| == |s.constants.all.config.replica_ids|
	}

  /** 0 + 19 */
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
		SeqIsAbstractable(s.received_1b_packets, AbstractifyCPacketToRslPacket) 
		&& 
		CReceived2avsIsAbstractable(s.received_2avs) 
		&& 
		COperationNumberIsAbstractable(s.opn_to_be_send_2b) 
		&& 
		CValToBeSent2bIsAbstractable(s.val_to_be_sent_2b)
	}

  /** 0 + 13 */
  function AbstractifyCAcceptorToLAcceptor(s: CAcceptor) : LAcceptor 
		requires CAcceptorIsAbstractable(s)
	{
		LAcceptor(
		AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), 
		AbstractifyCBallotToBallot(s.max_bal), 
		AbstractifyCVotesToVotes(s.votes), 
		AbstractifySeq(s.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), 
		AbstractifyCOperationNumberToOperationNumber(s.log_truncation_point), 
		AbstractifySeq(s.received_1b_packets, AbstractifyCPacketToRslPacket), 
		AbstractifyCReceived2avsToReceived2avs(s.received_2avs), 
		AbstractifyCOperationNumberToOperationNumber(s.opn_to_be_send_2b), 
		AbstractifyCValToBeSent2bToValToBeSent2b(s.val_to_be_sent_2b))
	}


	/** 6 + 6 + 10 */
  	function method CCountMatchedValInReceived2avs(s: seq<CPacket>, v: CRequestBatch) : int 
		requires (forall i :: i in s ==> CPacketIsValid(i))
		requires CRequestBatchIsValid(v)
		requires (forall p :: p in s ==> p.msg.CMessage_2av?)
		ensures 
			var lr := CountMatchedValInReceived2avs(
						AbstractifySeq(s, AbstractifyCPacketToRslPacket), 
						AbstractifyCRequestBatchToRequestBatch(v)); 
			var cr := CCountMatchedValInReceived2avs(s, v); 
			(cr) == (lr)
	{
		/* manually add */
		ghost var ls := AbstractifySeq(s, AbstractifyCPacketToRslPacket);
		ghost var lv := AbstractifyCRequestBatchToRequestBatch(v);
		if |s| == 0 then 
			0
		else 
			/* manually add */
			lemma_seq_sub(s, AbstractifyCPacketToRslPacket, 0, |s|-1);
			ghost var r_prev := CCountMatchedValInReceived2avs(s[..|s|-1], v);
			ghost var ls_prev := AbstractifySeq(s[..|s|-1], AbstractifyCPacketToRslPacket);
			ghost var lr_prev := CountMatchedValInReceived2avs(ls_prev, lv);
			assert r_prev == lr_prev;
			ghost var cur := if s[|s| - 1].msg.val_2av == v then 1 else 0;
			ghost var s_last := s[|s|-1];
			assert CPacketIsValid(s_last);
			CCountMatchedValInReceived2avs(s[ .. |s| - 1], v) + if s[|s| - 1].msg.val_2av == v then 1 else 0
	}

	/** 6 + 6 + 10 */
	function method CCountMatchedInRequestBatches(s: seq<CRequestBatch>, v: CRequestBatch) : int 
		requires (forall i :: i in s ==> CRequestBatchIsValid(i))
		requires CRequestBatchIsValid(v)
		ensures 
			var lr := CountMatchedInRequestBatches(
						AbstractifySeq(s, AbstractifyCRequestBatchToRequestBatch), 
						AbstractifyCRequestBatchToRequestBatch(v)); 
			var cr := CCountMatchedInRequestBatches(s, v); 
			(cr) == (lr)
	{
		/* manually add */
		ghost var ls := AbstractifySeq(s, AbstractifyCRequestBatchToRequestBatch);
		ghost var lv := AbstractifyCRequestBatchToRequestBatch(v);
		if |s| == 0 then 
			0 
		else 
			/* manually add */
			lemma_seq_sub(s, AbstractifyCRequestBatchToRequestBatch, 0, |s|-1);
			ghost var r_prev := CCountMatchedInRequestBatches(s[..|s|-1], v);
			ghost var ls_prev := AbstractifySeq(s[..|s|-1], AbstractifyCRequestBatchToRequestBatch);
			ghost var lr_prev := CountMatchedInRequestBatches(ls_prev, lv);
			assert r_prev == lr_prev;
			ghost var cur := if s[|s| - 1] == v then 1 else 0;
			ghost var s_last := s[|s|-1];
			assert CRequestBatchIsValid(s_last);
			CCountMatchedInRequestBatches(s[ .. |s| - 1], v) + if s[|s| - 1] == v then 1 else 0
	}

	/** 4 + 3 + 0 */
	function method CHasReceivedSame2avFromByzQuorum(r2avs: CAcceptorTuple, n: int) : bool 
		requires CAcceptorTupleIsValid(r2avs)
		requires (forall p :: p in r2avs.received_2av_packets ==> p.msg.CMessage_2av?)
		ensures var lr := HasReceivedSame2avFromByzQuorum(AbstractifyCAcceptorTupleToAcceptorTuple(r2avs), n); var cr := CHasReceivedSame2avFromByzQuorum(r2avs, n); (cr) == (lr)
	{
		(exists p :: p in r2avs.received_2av_packets && CCountMatchedValInReceived2avs(r2avs.received_2av_packets, p.msg.val_2av) >= n)
	}
	
	/** 4 + 2 + 0 */
	function method CIsByzQuorumSendSame2av(vals: seq<CRequestBatch>, n: int) : bool 
		requires (forall i :: i in vals ==> CRequestBatchIsValid(i))
		ensures var lr := IsByzQuorumSendSame2av(AbstractifySeq(vals, AbstractifyCRequestBatchToRequestBatch), n); var cr := CIsByzQuorumSendSame2av(vals, n); (cr) == (lr)
	{
		(exists v :: v in vals && CCountMatchedInRequestBatches(vals, v) >= n)
	}

	/** 4 + 3 + 0 */
	function method CHasReceived2avOfOpn(received_2avs: CReceived2avs, opn: COperationNumber) : bool 
		requires CReceived2avsIsValid(received_2avs)
		requires COperationNumberIsValid(opn)
		ensures var lr := HasReceived2avOfOpn(AbstractifyCReceived2avsToReceived2avs(received_2avs), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CHasReceived2avOfOpn(received_2avs, opn); (cr) == (lr)
	{
		opn in received_2avs
	}

	/** 4 + 4 + 1 */
	function method CAcceptorTupleIsUniqueSeq(tup:CAcceptorTuple) : bool
		requires CAcceptorTupleIsValid(tup)
		ensures 
			var lr := AcceptorTupleIsUniqueSeq(AbstractifyCAcceptorTupleToAcceptorTuple(tup));
			var cr := CAcceptorTupleIsUniqueSeq(tup); 
			(cr) == (lr)
	{
		/* manually add */
		lemma_CAcceptorTupleIsUniqueSeq(tup);
		(forall i, j :: 0 <= i < |tup.received_2av_packets| && 0 <= j < |tup.received_2av_packets| && i != j ==> tup.received_2av_packets[i] != tup.received_2av_packets[j] && tup.received_2av_packets[i].src != tup.received_2av_packets[j].src)
	}

	/** 6 + 5 + 0 */
	function method CReceived2avSetCorrect(r2avs: CAcceptorTuple, bal: CBallot, opn: COperationNumber, c: CConfiguration) : bool 
		requires CAcceptorTupleIsValid(r2avs)
		requires CBallotIsValid(bal)
		requires COperationNumberIsValid(opn)
		requires CConfigurationIsValid(c)
		ensures var lr := Received2avSetCorrect(AbstractifyCAcceptorTupleToAcceptorTuple(r2avs), AbstractifyCBallotToBallot(bal), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCConfigurationToLConfiguration(c)); var cr := CReceived2avSetCorrect(r2avs, bal, opn, c); (cr) == (lr)
	{
		|r2avs.received_2av_packets| <= |c.replica_ids|
		&& 
		(forall p :: p in r2avs.received_2av_packets ==> p.msg.CMessage_2av? && p.msg.opn_2av == opn && p.msg.bal_2av == bal && p.src in c.replica_ids)
	}
	
	/** 6 + 4 + 0 */
	function method CAcceptorStateCorrect(r2avs: CReceived2avs, bal: CBallot, c: CConfiguration) : bool 
		requires CReceived2avsIsValid(r2avs)
		requires CBallotIsValid(bal)
		requires CConfigurationIsValid(c)
		ensures var lr := AcceptorStateCorrect(AbstractifyCReceived2avsToReceived2avs(r2avs), AbstractifyCBallotToBallot(bal), AbstractifyCConfigurationToLConfiguration(c)); var cr := CAcceptorStateCorrect(r2avs, bal, c); (cr) == (lr)
	{
		(forall opn :: opn in r2avs ==> 
			&& CReceived2avSetCorrect(r2avs[opn], bal, opn, c)
			&& CAcceptorTupleIsUniqueSeq(r2avs[opn])
		)
	}

  /** 4 + 4 + 1 */
	function method CIsLogTruncationPointValid(log_truncation_point: COperationNumber, last_checkpointed_operation: seq<COperationNumber>, config: CConfiguration) : bool 
		requires COperationNumberIsValid(log_truncation_point)
		requires (forall i :: i in last_checkpointed_operation ==> COperationNumberIsValid(i))
		requires CConfigurationIsValid(config)
		ensures var lr := IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCConfigurationToLConfiguration(config)); var cr := CIsLogTruncationPointValid(log_truncation_point, last_checkpointed_operation, config); (cr) == (lr)
	{
		/* manually add */
    	assert AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber) == last_checkpointed_operation;
		IsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, CByzQuorumSize(config))
	}

  	/** 5 + 3 + 1 */
  	function method CRemoveVotesBeforeLogTruncationPoint(votes: CVotes, log_truncation_point: COperationNumber) : CVotes 
		requires CVotesIsValid(votes)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var votes' := CRemoveVotesBeforeLogTruncationPoint(votes, log_truncation_point); CVotesIsValid(votes') && RemoveVotesBeforeLogTruncationPoint(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
	{
		var t1 := (map opn | opn in votes && opn >= log_truncation_point :: votes[opn]); 	
		// lemma_voteLen(t1);	
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
    	// lemma_voteLen(t1);
		t1
	}

  	/** 11 + 2 */
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

	/** 5 + 2 */
	function method CAcceptorMaybeEnterNewView(s: CAcceptor) : CAcceptor 
		requires CAcceptorIsValid(s)
		ensures var s' := CAcceptorMaybeEnterNewView(s); CAcceptorIsValid(s') && LAcceptorMaybeEnterNewView(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'))
	{
		var t1 := 
			s.(received_1b_packets := []); 		
		t1
	}

  	/** 18 + 4 */
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
						Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1b(m.bal_1a, s.log_truncation_point, s.votes))); 					
					var t2 := 
						s.(max_bal := m.bal_1a); 					
					(t2, t1) 
				else 
					var t1 := 
						s; 					
					var t2 := 
						Broadcast(CBroadcastNop); 					
					(t1, t2); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	/** 5 + 6 */
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

	/** 27 + 7 */
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
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2av(m.bal_1c, m.opn_1c, m.val_1c))); 				
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

	/** 57 + 4 + 12 */
	function method CAcceptorProcess2av(s: CAcceptor, inp: CPacket) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_2av?
		ensures var s' := CAcceptorProcess2av(s, inp); CAcceptorIsValid(s') && LAcceptorProcess2av(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		/* manual annotations */
		lemma_AbstractifyMap_properties(s.received_2avs, AbstractifyCOperationNumberToOperationNumber, AbstractifyCAcceptorTupleToAcceptorTuple, AbstractifyOperationNumberToCOperationNumber);
		ghost var ss := AbstractifyCAcceptorToLAcceptor(s);
    	ghost var p := AbstractifyCPacketToRslPacket(inp);
		
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
									/* manual annotations */
            						assert CAcceptorTupleIsAbstractable(tup');
									var t' := AcceptorTuple([p]);
            						assert t' == AbstractifyCAcceptorTupleToAcceptorTuple(tup');

									var t1 := 
										s.(max_bal := m.bal_2av, received_2avs := map[opn:= tup']); 									
									t1; 								
								t1 
							else 
								var t1 := 
									if opn !in s.received_2avs then 
										var t1 := 
											var tup' := 
												CAcceptorTuple([inp]); 		
												/* manual annotations */
												assert CAcceptorTupleIsAbstractable(tup');
												var t' := AcceptorTuple([p]);
												assert t' == AbstractifyCAcceptorTupleToAcceptorTuple(tup');

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
														/* manual annotations */
                        								var t := ss.received_2avs[opn];
														var t' := t.(received_2av_packets := t.received_2av_packets + [p]);
														assert t' == AbstractifyCAcceptorTupleToAcceptorTuple(tup');

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

	/** 6 + 8 */
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

	/** 42 + 4 */
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
							Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2b(bal, opn, v))); 						
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
							s.(opn_to_be_send_2b := s.opn_to_be_send_2b + 1, 
								val_to_be_sent_2b := CValToBeSent2bUnknown(), 
								votes := t2.0, 
								log_truncation_point := t2.1); 						
						(t3, t1); 					
					(t1.1, t1.0); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	/** 12 + 3 */
	function method CAcceptorForgetReceived2avs(s: CAcceptor, opn: COperationNumber) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CAcceptorForgetReceived2avs(s, opn); CAcceptorIsValid(s') && LAcceptorForgetReceived2avs(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		var t1 := 
			if opn in s.received_2avs then 
				var t1 := 
					s.(received_2avs := RemoveElt(s.received_2avs, opn)); 				
				t1 
			else 
				var t1 := 
					s; 				
				t1; 		
		t1
	}

  	/** 23 + 4 */
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

	/** 15 + 3 */
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

  /************************** AutoMan Translation End ********************/ 

	/************************ Manual code for I0 *************************/
	/** 0 + 0 + 10 */
	lemma lemma_AcceptorTupleIsUniqueSeq(tup:CAcceptorTuple, ltup:AcceptorTuple)
		requires CAcceptorTupleIsValid(tup)
		requires ltup == AbstractifyCAcceptorTupleToAcceptorTuple(tup)
		ensures (forall i, j :: 0 <= i < |tup.received_2av_packets| && 0 <= j < |tup.received_2av_packets| && i != j ==> tup.received_2av_packets[i] != tup.received_2av_packets[j] && tup.received_2av_packets[i].src != tup.received_2av_packets[j].src) ==
				(forall i, j :: 0 <= i < |ltup.received_2av_packets| && 0 <= j < |ltup.received_2av_packets| && i != j ==> ltup.received_2av_packets[i] != ltup.received_2av_packets[j] && ltup.received_2av_packets[i].src != ltup.received_2av_packets[j].src)
	{
		var p2avs := tup.received_2av_packets;
		var lp2avs := ltup.received_2av_packets;
		assert lp2avs == AbstractifySeq(p2avs, AbstractifyCPacketToRslPacket);
		assert forall i :: i in p2avs ==> AbstractifyCPacketToRslPacket(i) in lp2avs;
	}

	/** 0 + 0 + 8 */
	lemma lemma_CAcceptorTupleIsUniqueSeq(tup:CAcceptorTuple)
		requires CAcceptorTupleIsValid(tup)
		ensures var lr := AcceptorTupleIsUniqueSeq(AbstractifyCAcceptorTupleToAcceptorTuple(tup));
				var cr := (forall i, j :: 0 <= i < |tup.received_2av_packets| && 0 <= j < |tup.received_2av_packets| && i != j ==> tup.received_2av_packets[i] != tup.received_2av_packets[j] && tup.received_2av_packets[i].src != tup.received_2av_packets[j].src); 
				(cr) == (lr)
	{
		var ltup := AbstractifyCAcceptorTupleToAcceptorTuple(tup);
		lemma_AcceptorTupleIsUniqueSeq(tup, ltup);
	}

	/************************ Manual code for I0 end *************************/

	// lemma {:axiom} lemma_voteLen(votes:CVotes)
	// 	ensures |votes| < max_votes_len()
}
