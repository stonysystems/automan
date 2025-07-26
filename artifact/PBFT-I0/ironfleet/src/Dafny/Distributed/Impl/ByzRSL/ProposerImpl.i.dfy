include "AppInterface.i.dfy"
include "../../Protocol/ByzRSL/Proposer.i.dfy"
include "ElectionImpl.i.dfy"
include "Broadcast.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "ElectionImpl.i.dfy"
include "CConstants.i.dfy"
include "CheckValSafetyImpl.i.dfy"

module LiveByzRSL__ProposerModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__Broadcast_i
  import opened LiveByzRSL__CMessage_i
  import opened LiveByzRSL__CheckValSafetyImpl_i
  import opened LiveByzRSL__Configuration_i
  import opened LiveByzRSL__ConstantsState_i
  import opened LiveByzRSL__CConfiguration_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__Election_i
  import opened LiveByzRSL__ElectionModel_i
  import opened LiveByzRSL__Message_i
  import opened LiveByzRSL__PacketParsing_i
  import opened LiveByzRSL__Proposer_i
  import opened LiveByzRSL__Types_i
  import opened LiveByzRSL__CheckValSafety_i
  import opened Impl__LiveByzRSL__Broadcast_i
  import opened Collections__Maps_i
  import opened Collections__Sets_i
  import opened Common__NodeIdentity_i
  import opened Common__SeqIsUnique_i
  import opened Common__SeqIsUniqueDef_i
  import opened Common__UdpClient_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened GenericRefinement_i
  import opened Environment_s
  import opened LiveByzRSL__Environment_i
  // import opened LiveRSL__Proposer_i

/************************** AutoMan Translation ************************/

  /** 7 + 0 */
	datatype CIncompleteBatchTimer = 
	CIncompleteBatchTimerOn(
		when: int
	)
	 | 
	CIncompleteBatchTimerOff(
		
	)

  /** 0 + 6 */
	predicate CIncompleteBatchTimerIsValid(s: CIncompleteBatchTimer) 
	{
		match s
		case CIncompleteBatchTimerOn(when) => CIncompleteBatchTimerIsAbstractable(s)
		case CIncompleteBatchTimerOff() => CIncompleteBatchTimerIsAbstractable(s)
	}

  /** 0 + 6 */
	predicate CIncompleteBatchTimerIsAbstractable(s: CIncompleteBatchTimer) 
	{
		match s
		case CIncompleteBatchTimerOn(when) => true
		case CIncompleteBatchTimerOff() => true
	}

  /** 0 + 7 */
	function AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(s: CIncompleteBatchTimer) : IncompleteBatchTimer 
		requires CIncompleteBatchTimerIsAbstractable(s)
	{
		match s
		case CIncompleteBatchTimerOn(when) => IncompleteBatchTimerOn(s.when)
		case CIncompleteBatchTimerOff => IncompleteBatchTimerOff()
	}

  /** 12 + 0 */
  datatype CProposer = 
	CProposer(
		constants: CReplicaConstants, 
		current_state: int, 
		request_queue: seq<CRequest>, 
		max_ballot_i_sent_1a: CBallot, 
		next_operation_number_to_propose: int, 
		received_1b_packets: seq<CPacket>, 
		highest_seqno_requested_by_client_this_view: map<EndPoint, int>, 
		incomplete_batch_timer: CIncompleteBatchTimer, 
		election_state: CElectionState
	)

  /** 0 + 16 + 3 */
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
		(forall i :: i in s.received_1b_packets ==> CPacketIsValid(i)) 
		&& 
		(forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsValid(i)) 
		&& 
		CIncompleteBatchTimerIsValid(s.incomplete_batch_timer) 
		&& 
		CElectionStateIsValid(s.election_state)
    // /** Manually Added */
    &&
    (forall p :: p in s.received_1b_packets ==>
            	   && CPacketIsValid(p)
                   && p.msg.CMessage_1b?
                   && p.msg.bal_1b == s.max_ballot_i_sent_1a
                   && CVotesIsValid(p.msg.votes))
    &&
    s.constants == s.election_state.constants
    &&
    CRequestBatchIsValid(s.request_queue)
	}

  /** 0 + 16 */
	predicate CProposerIsAbstractable(s: CProposer) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		(forall i :: i in s.request_queue ==> CRequestIsAbstractable(i)) 
		&& 
		CBallotIsAbstractable(s.max_ballot_i_sent_1a) 
		&& 
		(forall i :: i in s.received_1b_packets ==> CPacketIsAbstractable(i)) 
		&& 
		(forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsAbstractable(i)) 
		&& 
		CIncompleteBatchTimerIsAbstractable(s.incomplete_batch_timer) 
		&& 
		CElectionStateIsAbstractable(s.election_state)
	}

  /** 0 + 15 */
  function AbstractifyCProposerToLProposer(s: CProposer) : LProposer 
    requires CProposerIsValid(s)
		// requires CProposerIsAbstractable(s)
	{
		LProposer(
      AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), 
      s.current_state, 
      AbstractifySeq(s.request_queue, AbstractifyCRequestToRequest), 
      AbstractifyCBallotToBallot(s.max_ballot_i_sent_1a), 
      s.next_operation_number_to_propose, 
      AbstractifySeq(s.received_1b_packets, AbstractifyCPacketToRslPacket), 
      AbstractifyMap(s.highest_seqno_requested_by_client_this_view, AbstractifyEndPointToNodeIdentity, NoChange, AbstractifyNodeIdentityToEndPoint), 
      AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(s.incomplete_batch_timer), 
      AbstractifyCElectionStateToElectionState(s.election_state))
	}

  /** 4 + 3 */
  function method CIsAfterLogTruncationPoint(opn: COperationNumber, S: seq<CPacket>) : bool 
		requires COperationNumberIsValid(opn)
		requires (forall i :: i in S ==> CPacketIsValid(i))
		ensures var lr := LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySeq(S, AbstractifyCPacketToRslPacket)); var cr := CIsAfterLogTruncationPoint(opn, S); (cr) == (lr)
	{
		(forall p :: p in S && p.msg.CMessage_1b? ==> p.msg.log_truncation_point <= opn)
	}

  /** 18 + 4 */
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
		CLtUpperBound(opn, s.constants.all.params.max_integer_val)
	}

  /** 21 + 2 */
  function method CProposerInit(c: CReplicaConstants) : CProposer 
		requires CReplicaConstantsIsValid(c)
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

  /** 19 + 4 */
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
    // lemma_RequestQueue_len(t1.request_queue); /* Axiom Lemma */
		t1
	}

  /** 17 + 2 */
  function method CProposerMaybeEnterNewViewAndSend1a(s: CProposer) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		ensures var (s', broadcast_sent_packets) := CProposerMaybeEnterNewViewAndSend1a(s); CProposerIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LProposerMaybeEnterNewViewAndSend1a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := 
			if s.election_state.current_view.proposer_id == s.constants.my_index && CBalLt(s.max_ballot_i_sent_1a, s.election_state.current_view) then 
				var t1 := 
					s.(current_state := 1, max_ballot_i_sent_1a := s.election_state.current_view, received_1b_packets := [], highest_seqno_requested_by_client_this_view := map[], request_queue := s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch); 				
				var t2 := 
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1a(s.election_state.current_view))); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
          Broadcast(CBroadcastNop); 				
				(t1, t2); 	
    // lemma_RequestQueue_len(t1.0.request_queue); /* Axiom Lemma */	
		(t1.0, t1.1)
	}

  /** 6 + 8 */
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

  /** 18 + 3 */
  function method CProposerMaybeEnterPhase2(s: CProposer, log_truncation_point: COperationNumber) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var (s', broadcast_sent_packets) := CProposerMaybeEnterPhase2(s, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LProposerMaybeEnterPhase2(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := 
			if |s.received_1b_packets| >= CByzQuorumSize(s.constants.all.config) && CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) && s.current_state == 1 then 
				var t1 := 
					s.(current_state := 2, next_operation_number_to_propose := log_truncation_point); 				
				var t2 := 
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_StartingPhase2(s.max_ballot_i_sent_1a, log_truncation_point))); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					Broadcast(CBroadcastNop); 				
				(t1, t2); 		
		(t1.0, t1.1)
	}

	/** 32 + 5 */
  	function method CProposerNominateNewValueAndSend1c(s: CProposer, clock: int, log_truncation_point: COperationNumber) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
		requires CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
		ensures var (s', broadcast_sent_packets) := CProposerNominateNewValueAndSend1c(s, clock, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LProposerNominateNewValueAndSend1c(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
    var batchSize := 
				if (|s.request_queue| <= s.constants.all.params.max_batch_size) || (s.constants.all.params.max_batch_size < 0) then 
					|s.request_queue| 
				else 
					s.constants.all.params.max_batch_size; 	
		var t1 := 
			var t1 := 
				var v := 
					s.request_queue[ .. batchSize]; 				
				var t1 := 
					var opn := 
						s.next_operation_number_to_propose; 					
					var t1 := 
						s.(
              request_queue := s.request_queue[batchSize .. ], 
              next_operation_number_to_propose := s.next_operation_number_to_propose + 1, 
              incomplete_batch_timer := 
                if |s.request_queue| > batchSize then 
                  CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)) 
                else 
                  CIncompleteBatchTimerOff()); 					
					var t2 := 
						Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1c(s.max_ballot_i_sent_1a, opn, v))); 					
					(t1, t2); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 	
      /* Manually added */
      lemma_seq_sub(s.request_queue, AbstractifyCRequestToRequest, 0, batchSize);	
		(t1.0, t1.1)
	}



  /** 20 + 4 */
  function method CProposerProcessHeartbeat(s: CProposer, p: CPacket, clock: int) : CProposer 
		requires CProposerIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_Heartbeat?
		ensures var s' := CProposerProcessHeartbeat(s, p, clock); CProposerIsValid(s') && LProposerProcessHeartbeat(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p), clock)
	{
		var t1 := 
			CElectionStateProcessHeartbeat(s.election_state, p, clock); 		
		var t2 := 
      if CBalLt(s.election_state.current_view, t1.current_view) then  
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
			s.(election_state := t1, current_state := t2.0, request_queue := t2.1); 		
		t3
	}

  /** 7 + 2 */
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

  /** 21 + 2 */
  function method CProposerCheckForQuorumOfViewSuspicions(s: CProposer, clock: int) : CProposer 
		requires CProposerIsValid(s)
		ensures var s' := CProposerCheckForQuorumOfViewSuspicions(s, clock); CProposerIsValid(s') && LProposerCheckForQuorumOfViewSuspicions(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	{
		var t1 := 
			CElectionStateCheckForQuorumOfViewSuspicions(s.election_state, clock); 		
		var t2 := 
      if CBalLt(s.election_state.current_view, t1.current_view) then
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
			s.(election_state := t1, current_state := t2.0, request_queue := t2.1); 		
		t3
	}


  /** 7 + 3 */
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

/************************** AutoMan Translation End ************************/

/************************** Manual Code For I0 ************************/



/** 17 + 39 */
method CProposerNominateOldValueAndSend1c(s:CProposer,log_truncation_point:COperationNumber) returns (s':CProposer, sent_packets:OutboundPackets)
requires CProposerIsValid(s)
requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
requires !CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
ensures CProposerIsValid(s')
ensures OutboundPacketsIsValid(sent_packets)
ensures OutboundPacketsHasCorrectSrc(sent_packets, s'.constants.all.config.replica_ids[s'.constants.my_index]) /** Manually Added */
ensures  LProposerNominateOldValueAndSend1c(AbstractifyCProposerToLProposer(s), 
                                            AbstractifyCProposerToLProposer(s'), 
                                            AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
                                            AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
{
  var opn := s.next_operation_number_to_propose;
  var byzq := CByzQuorumSize(s.constants.all.config);
  var wq := CMinQuorumSize(s.constants.all.config);

  ghost var ls := AbstractifyCProposerToLProposer(s);
  ghost var lopn := ls.next_operation_number_to_propose;
  ghost var lbyzq := LByzQuorumSize(ls.constants.all.config);
  ghost var lwq := LMinQuorumSize(ls.constants.all.config);
  assert byzq == lbyzq;
  assert wq == lwq;

  if (exists p :: p in s.received_1b_packets && opn in p.msg.votes
                  && CValIsSafeAt(p.msg.votes[opn].max_val, s.received_1b_packets, opn, byzq, wq))
  {
    
    var p :| p in s.received_1b_packets && opn in p.msg.votes
                  && CValIsSafeAt(p.msg.votes[opn].max_val, s.received_1b_packets, opn, byzq, wq);
    assert CValIsSafeAt(p.msg.votes[opn].max_val, s.received_1b_packets, opn, byzq, wq);
    assert LValIsSafeAt(AbstractifyCRequestBatchToRequestBatch(p.msg.votes[opn].max_val), 
                                        AbstractifySeq(s.received_1b_packets, AbstractifyCPacketToRslPacket),
                                        AbstractifyCOperationNumberToOperationNumber(opn),
                                        byzq,
                                        wq);
    // ghost var lp2 := AbstractifyCPacketToRslPacket(p);
    // assume lp2 in ls.received_1b_packets && lopn in lp2.msg.votes;

    // assert exists lp :: lp in ls.received_1b_packets && ls.next_operation_number_to_propose in lp.msg.votes
    //               && LValIsSafeAt(lp.msg.votes[ls.next_operation_number_to_propose].max_val, ls.received_1b_packets, ls.next_operation_number_to_propose, byzq, wq);

    // ghost var lp :| lp in ls.received_1b_packets && lopn in lp.msg.votes 
    //         && LValIsSafeAt(lp.msg.votes[lopn].max_val, /*s.max_ballot_i_sent_1a,*/ ls.received_1b_packets, lopn, lbyzq, lwq);

    // assert LValIsSafeAt(lp.msg.votes[opn].max_val, 
    //                     ls.received_1b_packets,
    //                     lopn,
    //                     lbyzq,
    //                     lwq);

    // var msg := CMessage_1c(s.max_ballot_i_sent_1a, opn, p.msg.votes[opn].max_val);
    // ghost var lmsg2 := AbstractifyCMessageToRslMessage(msg);
    // ghost var lmsg := RslMessage_1c(ls.max_ballot_i_sent_1a, lopn, lp.msg.votes[lopn].max_val);

    // assert lmsg2.bal_1c == lmsg.bal_1c;
    // assert lmsg2.opn_1c == lmsg.opn_1c;
    // assert lmsg2.val_1c == lmsg.val_1c;
    // assert lmsg2 == lmsg; 
    

    s' := s.(next_operation_number_to_propose := s.next_operation_number_to_propose + 1);
    sent_packets := Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1c(s.max_ballot_i_sent_1a, opn, p.msg.votes[opn].max_val)));
    
    // assert s.next_operation_number_to_propose == ls.next_operation_number_to_propose;
    // ghost var ls' := ls.(next_operation_number_to_propose := ls.next_operation_number_to_propose + 1);
    // assume s'.next_operation_number_to_propose == ls'.next_operation_number_to_propose;
    // ghost var ls2' := AbstractifyCProposerToLProposer(s');
    // assert ls2'.next_operation_number_to_propose == ls'.next_operation_number_to_propose;
    // assert ls2' == ls';

    lemma_CProposerNominateOldValueAndSend1c(s,log_truncation_point,s',sent_packets);
    // assert LProposerNominateOldValueAndSend1c(ls, 
    //                                         ls', 
    //                                         AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
    //                                         AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
    assert LProposerNominateOldValueAndSend1c(AbstractifyCProposerToLProposer(s), 
                                            AbstractifyCProposerToLProposer(s'), 
                                            AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
                                            AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  } else {
    s' := s;
    sent_packets := Broadcast(CBroadcastNop);
    lemma_CProposerNominateOldValueAndSend1c(s,log_truncation_point,s',sent_packets);
    assert LProposerNominateOldValueAndSend1c(AbstractifyCProposerToLProposer(s), 
                                            AbstractifyCProposerToLProposer(s'), 
                                            AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
                                            AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  }
}

/** 0 + 7 */
lemma {:axiom} lemma_CProposerNominateOldValueAndSend1c(s:CProposer,log_truncation_point:COperationNumber, s':CProposer, sent_packets:OutboundPackets)
  requires CProposerIsValid(s)
  requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
  requires !CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
  ensures CProposerIsValid(s')
  ensures OutboundPacketsIsValid(sent_packets)
  ensures  LProposerNominateOldValueAndSend1c(AbstractifyCProposerToLProposer(s), 
                                              AbstractifyCProposerToLProposer(s'), 
                                              AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
                                              AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))

/** 24 + 4 */
method CProposerMaybeNominateValueAndSend1c(proposer:CProposer, clock:int, log_truncation_point:COperationNumber) returns (proposer':CProposer, sent_packets:OutboundPackets)
  requires CProposerIsValid(proposer)
  ensures CProposerIsValid(proposer')
  ensures OutboundPacketsIsValid(sent_packets)
  ensures OutboundPacketsHasCorrectSrc(sent_packets, proposer'.constants.all.config.replica_ids[proposer'.constants.my_index]) /** Manually Added */
  ensures  LProposerMaybeNominateValueAndSend1c(AbstractifyCProposerToLProposer(proposer),
                                                AbstractifyCProposerToLProposer(proposer'),
                                                clock as int,
                                                AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                                AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
{
  if !CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point, proposer.next_operation_number_to_propose) {
    proposer' := proposer;
    sent_packets := Broadcast(CBroadcastNop);
    // assert LProposerMaybeNominateValueAndSend1c(AbstractifyCProposerToLProposer(proposer),
    //                                             AbstractifyCProposerToLProposer(proposer'),
    //                                             clock as int,
    //                                             AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
    //                                             AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  } else if !CAllAcceptorsHadNoProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose) {
    proposer', sent_packets := CProposerNominateOldValueAndSend1c(proposer, log_truncation_point);
    // assert LProposerMaybeNominateValueAndSend1c(AbstractifyCProposerToLProposer(proposer),
    //                                             AbstractifyCProposerToLProposer(proposer'),
    //                                             clock as int,
    //                                             AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
    //                                             AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  }
  else if
    // CExistsAcceptorHasProposalLargeThanOpn(proposer.received_1b_packets, proposer.next_operation_number_to_propose)
    || (|proposer.request_queue| >= proposer.constants.all.params.max_batch_size as int)
    || (|proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= proposer.incomplete_batch_timer.when)
  {
    // proposer', sent_packets := CProposerNominateNewValueAndSend1c(proposer, clock, log_truncation_point);
    var (proposer'_, sent_packets_) := CProposerNominateNewValueAndSend1c(proposer, clock, log_truncation_point);
    // print "I am leader\n";
    proposer' := proposer'_;
    sent_packets := sent_packets_;
    // assert LProposerMaybeNominateValueAndSend1c(AbstractifyCProposerToLProposer(proposer),
    //                                             AbstractifyCProposerToLProposer(proposer'),
    //                                             clock as int,
    //                                             AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
    //                                             AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  } else if |proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOff? {
    proposer' := proposer.(incomplete_batch_timer := CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, proposer.constants.all.params.max_batch_delay, proposer.constants.all.params.max_integer_val)));
    sent_packets := Broadcast(CBroadcastNop);
    // assert LProposerMaybeNominateValueAndSend1c(AbstractifyCProposerToLProposer(proposer),
    //                                             AbstractifyCProposerToLProposer(proposer'),
    //                                             clock as int,
    //                                             AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
    //                                             AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  } else {
    proposer' := proposer;
    sent_packets := Broadcast(CBroadcastNop);
    // assert LProposerMaybeNominateValueAndSend1c(AbstractifyCProposerToLProposer(proposer),
    //                                             AbstractifyCProposerToLProposer(proposer'),
    //                                             clock as int,
    //                                             AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
    //                                             AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  }
}

/************************** Manual Code For I0 End ************************/

  /* ----------------------------------------- */

//   lemma {:axiom} lemma_RequestQueue_len(s:seq<CRequest>)
//     ensures |s| <= RequestBatchSizeLimit()
}
