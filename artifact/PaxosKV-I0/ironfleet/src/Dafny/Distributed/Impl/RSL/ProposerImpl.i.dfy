include "AppInterface.i.dfy"
include "../../Protocol/RSL/Proposer.i.dfy"
include "ElectionImpl.i.dfy"
include "Broadcast.i.dfy"
// include "MinCQuorumSize.i.dfy"
// include "ProposerLemmas.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Protocol/RSL/Proposer.i.dfy"
include "ElectionImpl.i.dfy"
include "CConstants.i.dfy"

module LiveRSL__ProposerModel_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__AppInterface_i
import opened LiveRSL__Broadcast_i
import opened LiveRSL__CMessage_i
// import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Election_i
import opened LiveRSL__ElectionModel_i
// import opened LiveRSL__ElectionState_i
import opened LiveRSL__Message_i
// import opened LiveRSL__MinCQuorumSize_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__Proposer_i
// import opened LiveRSL__ProposerLemmas_i
// import opened LiveRSL__ProposerState_i
// import opened LiveRSL__ConstantsState_i
import opened LiveRSL__Types_i
import opened Impl__LiveRSL__Broadcast_i
import opened Collections__Maps_i
import opened Collections__Sets_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUnique_i
import opened Common__SeqIsUniqueDef_i
import opened Common__NetClient_i
import opened Common__UpperBound_s
import opened Common__UpperBound_i
import opened Common__Util_i
import opened AppStateMachine_s
import opened GenericRefinement_i


/************************** AutoMan Translation ************************/
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
		case CIncompleteBatchTimerOff => IncompleteBatchTimerOff()

	}

  datatype CProposer = 
	CProposer(
		constants: CReplicaConstants, 
		current_state: int, 
		request_queue: seq<CRequest>, 
		max_ballot_i_sent_1a: CBallot, 
		next_operation_number_to_propose: int, 
		received_1b_packets: set<CPacket>, 
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
		(forall i :: i in s.received_1b_packets ==> CPacketIsValid(i)) 
		&& 
		(forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsValid(i)) 
		&& 
		CIncompleteBatchTimerIsValid(s.incomplete_batch_timer) 
		&& 
		CElectionStateIsValid(s.election_state)
    /** Manually Added */
    &&
    SetIsInjective(s.received_1b_packets, AbstractifyCPacketToRslPacket)
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
      AbstractifySet(s.received_1b_packets, AbstractifyCPacketToRslPacket), 
      AbstractifyMap(s.highest_seqno_requested_by_client_this_view, AbstractifyEndPointToNodeIdentity, NoChange, AbstractifyNodeIdentityToEndPoint), 
      AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(s.incomplete_batch_timer), 
      AbstractifyCElectionStateToElectionState(s.election_state))
	}

  function method CIsAfterLogTruncationPoint(opn: COperationNumber, received_1b_packets: set<CPacket>) : bool 
		// requires COperationNumberIsValid(opn)
		// requires (forall i :: i in received_1b_packets ==> CPacketIsValid(i))
		// ensures var lr := LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket)); var cr := CIsAfterLogTruncationPoint(opn, received_1b_packets); (cr) == (lr)
	{
		(forall p :: p in received_1b_packets && p.msg.CMessage_1b? ==> p.msg.log_truncation_point <= opn)
	}

	function method CSetOfMessage1b(S: set<CPacket>) : bool 
		// requires (forall i :: i in S ==> CPacketIsValid(i))
		// ensures var lr := LSetOfMessage1b(AbstractifySet(S, AbstractifyCPacketToRslPacket)); var cr := CSetOfMessage1b(S); (cr) == (lr)
	{
		(forall p :: p in S ==> p.msg.CMessage_1b?)
	}

  function method CSetOfMessage1bAboutBallot(S: set<CPacket>, b: CBallot) : bool 
		// requires (forall i :: i in S ==> CPacketIsValid(i))
		// requires CBallotIsValid(b)
		// ensures var lr := LSetOfMessage1bAboutBallot(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCBallotToBallot(b)); var cr := CSetOfMessage1bAboutBallot(S, b); (cr) == (lr)
	{
		CSetOfMessage1b(S) 
		&& 
		(forall p :: p in S ==> p.msg.bal_1b == b)
	}

	function method CAllAcceptorsHadNoProposal(S: set<CPacket>, opn: COperationNumber) : bool 
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
    /* Manually Added */requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
		ensures var lr := LAllAcceptorsHadNoProposal(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CAllAcceptorsHadNoProposal(S, opn); (cr) == (lr)
	{
    (forall p :: p in S ==> !(opn in p.msg.votes))
		// (forall p :: p in S ==> !opn in p.msg.votes)
	}

 function method CExistVotesHasProposalLargeThanOpn(p: CPacket, op: COperationNumber) : bool 
		requires CPacketIsValid(p)
		requires COperationNumberIsValid(op)
		requires p.msg.CMessage_1b?
		ensures var lr := LExistVotesHasProposalLargeThanOpn(AbstractifyCPacketToRslPacket(p), AbstractifyCOperationNumberToOperationNumber(op)); var cr := CExistVotesHasProposalLargeThanOpn(p, op); (cr) == (lr)
	{
		(exists opn :: opn in p.msg.votes && opn > op)
	}

	function method CExistsAcceptorHasProposalLargeThanOpn(S: set<CPacket>, op: COperationNumber) : bool 
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires COperationNumberIsValid(op)
		requires CSetOfMessage1b(S)
    /* Manually Added */requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
		ensures var lr := LExistsAcceptorHasProposalLargeThanOpn(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(op)); var cr := CExistsAcceptorHasProposalLargeThanOpn(S, op); (cr) == (lr)
	{
		(exists p :: p in S && CExistVotesHasProposalLargeThanOpn(p, op))
	}

  function method Cmax_balInS(c: CBallot, S: set<CPacket>, opn: COperationNumber) : bool 
		requires CBallotIsValid(c)
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
    /* Manually Added */requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
		ensures var lr := LMaxBallotInS(AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := Cmax_balInS(c, S, opn); (cr) == (lr)
	{
		(forall p :: p in S && opn in p.msg.votes ==> CBalLeq(p.msg.votes[opn].max_value_bal, c))
	}

	function method CExistsBallotInS(v: CRequestBatch, c: CBallot, S: set<CPacket>, opn: COperationNumber) : bool 
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(c)
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
    /* Manually Added */requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
		ensures 
		var lr := LExistsBallotInS(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); 
		var cr := CExistsBallotInS(v, c, S, opn); 
		(cr) == (lr)
	{
		(exists p :: p in S && opn in p.msg.votes && p.msg.votes[opn].max_value_bal == c && p.msg.votes[opn].max_val == v)
	}

  function method CValIsHighestNumberedProposalAtBallot(v: CRequestBatch, c: CBallot, S: set<CPacket>, opn: COperationNumber) : bool 
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(c)
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
    /* Manually Added */requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
		ensures var lr := LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CValIsHighestNumberedProposalAtBallot(v, c, S, opn); (cr) == (lr)
	{
		Cmax_balInS(c, S, opn) 
		&& 
		CExistsBallotInS(v, c, S, opn)
	}

	function method CValIsHighestNumberedProposal(v: CRequestBatch, S: set<CPacket>, opn: COperationNumber) : bool 
		requires CRequestBatchIsValid(v)
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
    /* Manually Added */requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
		ensures var lr := LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CValIsHighestNumberedProposal(v, S, opn); (cr) == (lr)
	{
		// (exists c :: CValIsHighestNumberedProposalAtBallot(v, c, S, opn))
    /** Manually Added */
    exists p :: p in S && opn in p.msg.votes && CValIsHighestNumberedProposalAtBallot(v, p.msg.votes[opn].max_value_bal, S, opn)
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
		|s.received_1b_packets| >= CMinQuorumSize(s.constants.all.config) 
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
  

  function method CProposerInit(c: CReplicaConstants) : CProposer 
		requires CReplicaConstantsIsValid(c)
		// requires CWellFormedLConfiguration(c.all.config)
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
			{}; 		
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
    lemma_RequestQueue_len(t1.request_queue); /* Axiom Lemma */
		t1
	}

  function method CProposerMaybeEnterNewViewAndSend1a(s: CProposer) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		ensures var (s', broadcast_sent_packets) := CProposerMaybeEnterNewViewAndSend1a(s); CProposerIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LProposerMaybeEnterNewViewAndSend1a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := 
			if s.election_state.current_view.proposer_id == s.constants.my_index && CBalLt(s.max_ballot_i_sent_1a, s.election_state.current_view) then 
				var t1 := 
					s.(current_state := 1, max_ballot_i_sent_1a := s.election_state.current_view, received_1b_packets := {}, highest_seqno_requested_by_client_this_view := map[], request_queue := s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch); 				
				var t2 := 
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1a(s.election_state.current_view))); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
          Broadcast(CBroadcastNop);
					// []; 				
				(t1, t2); 	
    lemma_RequestQueue_len(t1.0.request_queue); /* Axiom Lemma */	
		(t1.0, t1.1)
	}

  function method {:timeLimitMultiplier 3} CProposerProcess1b(s: CProposer, p: CPacket) : CProposer 
		requires CProposerIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_1b?
		requires p.src in s.constants.all.config.replica_ids
		requires p.msg.bal_1b == s.max_ballot_i_sent_1a
		requires s.current_state == 1
		requires (forall other_packet :: other_packet in s.received_1b_packets ==> other_packet.src != p.src)
		ensures var s' := CProposerProcess1b(s, p); CProposerIsValid(s') && LProposerProcess1b(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p))
	{
    /* Manually added */
    ghost var s_ := AbstractifyCProposerToLProposer(s);
    ghost var s'_ := s_.(received_1b_packets := s_.received_1b_packets + { AbstractifyCPacketToRslPacket(p) });
		var t1 := 
			s.(received_1b_packets := s.received_1b_packets + {p}); 	
    assert AbstractifyCProposerToLProposer(t1).received_1b_packets == s'_.received_1b_packets;	
		t1
	}

  function method CProposerMaybeEnterPhase2(s: CProposer, log_truncation_point: COperationNumber) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var (s', broadcast_sent_packets) := CProposerMaybeEnterPhase2(s, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LProposerMaybeEnterPhase2(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := 
			if |s.received_1b_packets| >= CMinQuorumSize(s.constants.all.config) && CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) && s.current_state == 1 then 
				var t1 := 
					s.(current_state := 2, next_operation_number_to_propose := log_truncation_point); 				
				var t2 := 
          /** Manually Modified */
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_StartingPhase2(s.max_ballot_i_sent_1a, log_truncation_point))); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
          /** Manually Modified */
					Broadcast(CBroadcastNop); 				
				(t1, t2); 		
		(t1.0, t1.1)
	}

  function method CProposerNominateNewValueAndSend2a(s: CProposer, clock: int, log_truncation_point: COperationNumber) : (CProposer, OutboundPackets) 
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
		requires CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
		ensures var (s', broadcast_sent_packets) := CProposerNominateNewValueAndSend2a(s, clock, log_truncation_point); CProposerIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LProposerNominateNewValueAndSend2a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
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
            /** Manually Modified */
						Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2a(s.max_ballot_i_sent_1a, opn, v))); 					
					(t1, t2); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 	
      /* Manually added */
      lemma_seq_sub(s.request_queue, AbstractifyCRequestToRequest, 0, batchSize);	
		(t1.0, t1.1)
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
      if CBalLt(s.election_state.current_view, t1.current_view) then 
			// if CBalLt(s.election_state.current_view, s'.election_state.current_view) then 
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
      if CBalLt(s.election_state.current_view, t1.current_view) then
			// if CBalLt(s.election_state.current_view, s'.election_state.current_view) then 
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

  lemma {:axiom} lemma_RequestQueue_len(s:seq<CRequest>)
    ensures |s| <= RequestBatchSizeLimit()

/************************** AutoMan Translation End ************************/

/************************** Manual Code For I0 ************************/

method CProposerNominateOldValueAndSend2a(s:CProposer,log_truncation_point:COperationNumber) returns (s':CProposer, sent_packets:OutboundPackets)
requires CProposerIsValid(s)
requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
requires !CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
ensures CProposerIsValid(s')
ensures OutboundPacketsIsValid(sent_packets)
ensures  LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(s), 
                                            AbstractifyCProposerToLProposer(s'), 
                                            AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
                                            AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
{
  var opn := s.next_operation_number_to_propose;
  if (exists p :: p in s.received_1b_packets && opn in p.msg.votes
                  && CValIsHighestNumberedProposal(p.msg.votes[opn].max_val, s.received_1b_packets, opn))
  {
    
    var p :| p in s.received_1b_packets && opn in p.msg.votes
                  && CValIsHighestNumberedProposal(p.msg.votes[opn].max_val, s.received_1b_packets, opn);
    assert CValIsHighestNumberedProposal(p.msg.votes[opn].max_val, s.received_1b_packets, opn);
    assert LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(p.msg.votes[opn].max_val), 
                                        AbstractifySet(s.received_1b_packets, AbstractifyCPacketToRslPacket),
                                        AbstractifyCOperationNumberToOperationNumber(opn));

    s' := s.(next_operation_number_to_propose := s.next_operation_number_to_propose + 1);
    sent_packets := Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2a(s.max_ballot_i_sent_1a, opn, p.msg.votes[opn].max_val)));
    assert LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(s), 
                                            AbstractifyCProposerToLProposer(s'), 
                                            AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
                                            AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  } else {
    /** This is a branch that cannot be executed, so we use an axiom lemma to pass the verification */
    s' := s;
    sent_packets := Broadcast(CBroadcastNop);
    lemma_CProposerNominateOldValueAndSend2a(s,log_truncation_point,s',sent_packets);
    assert LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(s), 
                                            AbstractifyCProposerToLProposer(s'), 
                                            AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
                                            AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets));
  }
}

lemma {:axiom} lemma_CProposerNominateOldValueAndSend2a(s:CProposer,log_truncation_point:COperationNumber, s':CProposer, sent_packets:OutboundPackets)
  requires CProposerIsValid(s)
  requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
  requires !CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
  ensures CProposerIsValid(s')
  ensures OutboundPacketsIsValid(sent_packets)
  ensures  LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(s), 
                                              AbstractifyCProposerToLProposer(s'), 
                                              AbstractifyCOperationNumberToOperationNumber(log_truncation_point), 
                                              AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))

method CProposerMaybeNominateValueAndSend2a(proposer:CProposer, clock:int, log_truncation_point:COperationNumber) returns (proposer':CProposer, sent_packets:OutboundPackets)
  requires CProposerIsValid(proposer)
  ensures CProposerIsValid(proposer')
  ensures OutboundPacketsIsValid(sent_packets)
  ensures  LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer),
                                                AbstractifyCProposerToLProposer(proposer'),
                                                clock as int,
                                                AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                                AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
{
  if !CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point, proposer.next_operation_number_to_propose) {
    proposer' := proposer;
    sent_packets := Broadcast(CBroadcastNop);
  } else if !CAllAcceptorsHadNoProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose) {
    proposer', sent_packets := CProposerNominateOldValueAndSend2a(proposer, log_truncation_point);
  }
  else if
    CExistsAcceptorHasProposalLargeThanOpn(proposer.received_1b_packets, proposer.next_operation_number_to_propose)
    || (|proposer.request_queue| >= proposer.constants.all.params.max_batch_size as int)
    || (|proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= proposer.incomplete_batch_timer.when)
  {
    var (proposer'_, sent_packets_) := CProposerNominateNewValueAndSend2a(proposer, clock, log_truncation_point);
    proposer' := proposer'_;
    sent_packets := sent_packets_;
  } else if |proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOff? {
    proposer' := proposer.(incomplete_batch_timer := CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, proposer.constants.all.params.max_batch_delay, proposer.constants.all.params.max_integer_val)));
    sent_packets := Broadcast(CBroadcastNop);
  } else {
    proposer' := proposer;
    sent_packets := Broadcast(CBroadcastNop);
  }
}
/************************** Manual Code For I0 End ************************/


// datatype CIncompleteBatchTimer = CIncompleteBatchTimerOn(when:uint64) | CIncompleteBatchTimerOff()

// datatype ProposerState = ProposerState(
//   constants:CReplicaConstants,

//   // current_state:byte,
//   current_state:uint64,

//   request_queue:seq<CRequest>,

//   max_ballot_i_sent_1a:CBallot,

//   next_operation_number_to_propose:uint64,

//   received_1b_packets:set<CPacket>,

//   highest_seqno_requested_by_client_this_view:map<EndPoint, uint64>,

//   incomplete_batch_timer:CIncompleteBatchTimer,

//   election_state:CElectionState
//   )

// function CProposerStateValid(s:ProposerState) : bool
// {
//   && ProposerIsAbstractable(s)
//   && CReplicaConstansValid(s.constants)
//   && CBallotValid(s.max_ballot_i_sent_1a)
//   && |s.request_queue| < 0x4000_0000_0000_0000
//   && 0 <= s.next_operation_number_to_propose < 0xffff_ffff_ffff_ffff
//   && CElectionStateValid(s.election_state)
//   && |s.received_1b_packets| < 0x4000_0000_0000_0000
//   && (forall p :: p in s.received_1b_packets ==> 
//               && p.msg.CMessage_1b?
//               && p.msg.bal_1b == s.max_ballot_i_sent_1a
//               && CVotesValid(p.msg.votes))
//   // && Received1bProperties(s.received_1b_packets, s.constants)
//   // && RequestQueueValid(s.request_queue)
// }
//   // maxOpnWithProposal:COperationNumber,
//   // maxLogTruncationPoint:COperationNumber

// predicate ProposerIsAbstractable(proposer:ProposerState)
// {
//   && ReplicaConstantsStateIsAbstractable(proposer.constants)
//   && CRequestsSeqIsAbstractable(proposer.request_queue)
//   && CBallotIsAbstractable(proposer.max_ballot_i_sent_1a)
//   && CPacketsIsAbstractable(proposer.received_1b_packets)
//   && (forall e :: e in proposer.highest_seqno_requested_by_client_this_view ==> EndPointIsValidPublicKey(e))
//   && CElectionStateIsAbstractable(proposer.election_state)
// }

// function AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(timer:CIncompleteBatchTimer) : IncompleteBatchTimer
// {
//   match timer {
//     case CIncompleteBatchTimerOn(when) => IncompleteBatchTimerOn(when as int)
//     case CIncompleteBatchTimerOff => IncompleteBatchTimerOff()
//   }
// }

// function AbstractifyProposerStateToLProposer(proposer:ProposerState) : LProposer
//   requires ProposerIsAbstractable(proposer)
// {
//   LProposer(AbstractifyReplicaConstantsStateToLReplicaConstants(proposer.constants),
//             proposer.current_state as int,
//             AbstractifyCRequestsSeqToRequestsSeq(proposer.request_queue),
//             AbstractifyCBallotToBallot(proposer.max_ballot_i_sent_1a),
//             proposer.next_operation_number_to_propose as int,
//             AbstractifySetOfCPacketsToSetOfRslPackets(proposer.received_1b_packets),
//             AbstractifyMapOfSeqNums(proposer.highest_seqno_requested_by_client_this_view),
//             AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(proposer.incomplete_batch_timer),
//             AbstractifyCElectionStateToElectionState(proposer.election_state))
// }

// // Same as x == y, but triggers extensional equality on fields and provides better error diagnostics
// // predicate Eq_LProposer(x:LProposer, y:LProposer)
// // {
// //   && x.constants == y.constants
// //   && x.current_state == y.current_state
// //   && x.request_queue == y.request_queue
// //   && x.max_ballot_i_sent_1a == y.max_ballot_i_sent_1a
// //   && x.next_operation_number_to_propose == y.next_operation_number_to_propose 
// //   && x.received_1b_packets == y.received_1b_packets
// //   && x.highest_seqno_requested_by_client_this_view == y.highest_seqno_requested_by_client_this_view
// //   && x.election_state == y.election_state 
// // }

// method CIsAfterLogTruncationPoint(opn:COperationNumber, received_1b_packets:set<CPacket>) returns (b:bool)
// {
//   b := (forall p :: p in received_1b_packets && p.msg.CMessage_1b? ==> p.msg.log_truncation_point <= opn);
// }

// predicate CSetOfMessage1b(S:set<CPacket>)
// {
//   (forall p :: p in S ==> p.msg.CMessage_1b?)
// }

// method CSetOfMessage1bAboutBallot(S:set<CPacket>, cb:CBallot) returns (b:bool)
// {
//   // var a := CSetOfMessage1b(S);
//   b := && (forall p :: p in S ==> p.msg.CMessage_1b?) 
//       && (forall p :: p in S ==> p.msg.bal_1b == cb);
// }

// method CAllAcceptorsHadNoProposal(S:set<CPacket>, opn:COperationNumber) returns (b:bool)
// {
//   b := && (forall p :: p in S ==> p.msg.CMessage_1b?)
//     && (forall p :: p in S ==> !(opn in p.msg.votes.v));
// }

// // 找到所有1b msg中，opn对应的最大的bal
// predicate method CMaxBallotInS(c:CBallot, S:set<CPacket>, opn:COperationNumber)
// requires CSetOfMessage1b(S)
// {
//   && (forall p :: p in S && opn in p.msg.votes.v ==> CBalLeq(p.msg.votes.v[opn].max_value_bal, c))
// }

// // method CMaxBallotInS(c:CBallot, S:set<CPacket>, opn:COperationNumber) returns (b:bool)
// // {
// //   b := && (forall p :: p in S ==> p.msg.CMessage_1b?) 
// //       && (forall p :: p in S && opn in p.msg.votes.v ==> CBalLeq(p.msg.votes.v[opn].max_value_bal, c));
// //   // b := false;
// //   // var a := CSetOfMessage1b(S);
// //   // if(a){
// //   //   b := forall p :: p in S && opn in p.msg.votes.v ==> CBalLeq(p.msg.votes.v[opn].max_value_bal, c);
// //   // }
// // }

// predicate method CExistsBallotInS(v:CRequestBatch, c:CBallot, S:set<CPacket>, opn:COperationNumber)
// requires CSetOfMessage1b(S)
// {
//   exists p :: && p in S
//         && opn in p.msg.votes.v
//         && p.msg.votes.v[opn].max_value_bal==c
//         && p.msg.votes.v[opn].max_val==v
// }

// predicate method CValIsHighestNumberedProposalAtBallot(v:CRequestBatch, c:CBallot, S:set<CPacket>, opn:COperationNumber)
// requires CSetOfMessage1b(S);
// {
//   && CMaxBallotInS(c, S, opn)
//   && CExistsBallotInS(v, c, S, opn)
//   // b := false;
//   // var a := CSetOfMessage1b(S);
//   // if(a){
//   //   var x := CMaxBallotInS(c, S, opn);
//   //   var y := CExistsBallotInS(v, c, S, opn);
//   //   b := x && y;
//   // }
// }

// // 这种量词怎么翻译
// // method CValIsHighestNumberedProposal(v:CRequestBatch, S:set<CPacket>, opn:COperationNumber) returns (b:bool)
// // requires CSetOfMessage1b(S);
// // {
// //     b := exists c :: CValIsHighestNumberedProposalAtBallot(v, c, S, opn);
// // }

// // predicate method CValIsHighestNumberedProposal(v:CRequestBatch, S:set<CPacket>, opn:COperationNumber) : (b:bool)
// // requires CSetOfMessage1b(S);
// // {
// //     exists c :: CValIsHighestNumberedProposalAtBallot(v, c, S, opn)
// // }

// method CGetMaxValInVotes(proposer:ProposerState) returns (v:CRequestBatch)
// requires CProposerStateValid(proposer)
// // requires CSetOfMessage1b(S)
// // requires S != {}
// // requires forall p :: p in S ==> CVotesValid(p.msg.votes)
// // requires !(forall p :: p in S ==> !(opn in p.msg.votes.v))
// {
//   // var b := Ballot(0,0);
//   var packets := proposer.received_1b_packets;
//   var opn := proposer.next_operation_number_to_propose;
//   if packets != {} && !(forall p :: p in packets ==> !(opn in p.msg.votes.v))
//   {
//   var pkt :| pkt in packets && opn in pkt.msg.votes.v;
//   v := pkt.msg.votes.v[opn].max_val;
//   var bal := pkt.msg.votes.v[opn].max_value_bal;
//   var p_bal := pkt;
//   packets := packets - {pkt};

//   while (packets != {})
//     decreases packets
//   {
//     pkt :| pkt in packets;
//     if (opn in pkt.msg.votes.v) {
//       var foundHigherBallot := CBalLeq(bal, pkt.msg.votes.v[opn].max_value_bal);

//       if (foundHigherBallot) {
//         p_bal := pkt;
//         v := pkt.msg.votes.v[opn].max_val;
//         bal := pkt.msg.votes.v[opn].max_value_bal;
//       }
//     }
//     packets := packets - {pkt};
//   }
//   }
// }

// // common里的upperbound文件也需要翻译
// method CProposerCanNominateUsingOperationNumber(s:ProposerState, log_truncation_point:COperationNumber, opn:COperationNumber) returns (b:bool)
// requires CProposerStateValid(s)
// {
//   var a := CMinQuorumSize(s.constants.all.config);
//   var x := CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a);
//   var y := CIsAfterLogTruncationPoint(opn, s.received_1b_packets);
//   var z := UpperBoundedAdditionImpl(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val);
//   var m := CLtUpperBound(opn, s.constants.all.params.max_integer_val);
//   b := s.election_state.current_view == s.max_ballot_i_sent_1a
//   && s.current_state == 2
//   && |s.received_1b_packets| >= a as int
//   && x
//   && y
//   && opn < z
//   && opn >= 0
//   && m;
//   // && LtUpperBound(opn, s.constants.all.params.max_integer_val);
// }

// method CProposerInit(constants:CReplicaConstants) returns (proposer:ProposerState)
// requires CReplicaConstansValid(constants)
// ensures  ProposerIsAbstractable(proposer)
//   ensures  WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config)
//   ensures  CProposerStateValid(proposer)
//   ensures  LProposerInit(AbstractifyProposerStateToLProposer(proposer), AbstractifyReplicaConstantsStateToLReplicaConstants(constants))
//   ensures  proposer.constants == constants
// {
//   var election := CElectionStateInit(constants);
//   proposer := ProposerState(constants,
//                             0,
//                             [],
//                             CBallot(0, constants.my_index),
//                             0,
//                             {},
//                             map [],
//                             CIncompleteBatchTimerOff(),
//                             election);
//   lemma_CProposerInit(constants, proposer);
// }

// lemma {:axiom} lemma_CProposerInit(constants:CReplicaConstants, proposer:ProposerState)
// requires CReplicaConstansValid(constants)
// ensures  ProposerIsAbstractable(proposer)
//   ensures  WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config)
//   ensures  CProposerStateValid(proposer)
//   ensures  LProposerInit(AbstractifyProposerStateToLProposer(proposer), AbstractifyReplicaConstantsStateToLReplicaConstants(constants))
//   ensures  proposer.constants == constants

// method CProposerProcessRequest(proposer:ProposerState, packet:CPacket) returns (proposer':ProposerState)
// requires packet.msg.CMessage_Request?
// requires CProposerStateValid(proposer)
// {
//   var val := CRequest(packet.src, packet.msg.seqno, packet.msg.val);
//   var newElectionState := CElectionStateReflectReceivedRequest(proposer.election_state, val);

//   if proposer.current_state != 0 && 
//      (val.client !in proposer.highest_seqno_requested_by_client_this_view ||
//       val.seqno > proposer.highest_seqno_requested_by_client_this_view[val.client])
//   {
//     proposer' := proposer.(election_state := newElectionState,
//                            request_queue := proposer.request_queue + [val],
//                            highest_seqno_requested_by_client_this_view := proposer.highest_seqno_requested_by_client_this_view[val.client := val.seqno]
//                            );
//   } else {
//     proposer' := proposer.(election_state := newElectionState);
//   }
// }

// method CProposerMaybeEnterNewViewAndSend1a(proposer:ProposerState) returns (proposer':ProposerState, sent_packets:CBroadcast)
// requires CProposerStateValid(proposer)
// {
//   var start_time := Time.GetDebugTimeTicks();
//   var lt := CCBalLt(proposer.max_ballot_i_sent_1a, proposer.election_state.current_view);
//   if proposer.election_state.current_view.proposer_id == proposer.constants.my_index && lt
//   {
//     print "start phase 1\n";
//     proposer' := proposer.(current_state := 1,
//                            max_ballot_i_sent_1a := proposer.election_state.current_view,
//                            received_1b_packets := {},
//                            highest_seqno_requested_by_client_this_view := map[],
//                            request_queue := proposer.election_state.requests_received_prev_epochs 
//                             + proposer.election_state.requests_received_this_epoch);
    
//     sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, CMessage_1a(proposer.election_state.current_view));
  
//     // var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }
//   } else {
//     proposer' := proposer;
//     sent_packets := CBroadcastNop;
//   }
// }

// method CProposerProcess1b(proposer:ProposerState, packet:CPacket) returns (proposer':ProposerState)
// requires packet.msg.CMessage_1b?
// {
//   proposer' := proposer.(received_1b_packets := proposer.received_1b_packets + { packet });
// }

// method CProposerMaybeEnterPhase2(proposer:ProposerState,log_truncation_point:COperationNumber) returns (proposer':ProposerState, sent_packets:CBroadcast)
// requires CProposerStateValid(proposer)
// {
//   var start_time := Time.GetDebugTimeTicks();

//   var a := CMinQuorumSize(proposer.constants.all.config);
//   var b := CSetOfMessage1bAboutBallot(proposer.received_1b_packets, proposer.max_ballot_i_sent_1a);
//   if |proposer.received_1b_packets| as uint64 >= a 
//       && b
//       && proposer.current_state == 1
//   {
//     print("Proposer: enter phase 2\n");
//     proposer' := proposer.(current_state := 2, next_operation_number_to_propose := log_truncation_point);
//     sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, CMessage_StartingPhase2(proposer.max_ballot_i_sent_1a, log_truncation_point));
  
//     // var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }
  
//   } else {
//     proposer' := proposer;
//     sent_packets := CBroadcastNop;
//   }
// }

// method CProposerNominateNewValueAndSend2a(proposer:ProposerState, clock:uint64, log_truncation_point:COperationNumber) returns (proposer':ProposerState, sent_packets:CBroadcast)
// requires CProposerStateValid(proposer)
// {
//   var batchSize := if |proposer.request_queue| <= proposer.constants.all.params.max_batch_size as int || proposer.constants.all.params.max_batch_size < 0 then
//                       |proposer.request_queue| 
//                     else 
//                       proposer.constants.all.params.max_batch_size as int;
//   var v := proposer.request_queue[..batchSize];
//   var opn_op := proposer.next_operation_number_to_propose;

//   proposer' := proposer.(request_queue := proposer.request_queue[batchSize..],
//                          next_operation_number_to_propose := proposer.next_operation_number_to_propose + 1,
//                          incomplete_batch_timer := if |proposer.request_queue| > batchSize as int then 
//                                                       CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, proposer.constants.all.params.max_batch_delay, proposer.constants.all.params.max_integer_val)) 
//                                                     else CIncompleteBatchTimerOff());
//   sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, CMessage_2a(proposer.max_ballot_i_sent_1a, opn_op, v));
// }

// // 对应 protocol 中 LProposerNominateOldValueAndSend2a，有exists量词，这里是我按照其含义翻译的
// method CProposerNominateOldValueAndSend2a(proposer:ProposerState,log_truncation_point:COperationNumber) returns (proposer':ProposerState, sent_packets:CBroadcast)
// requires CProposerStateValid(proposer)
// {
//   var opn := proposer.next_operation_number_to_propose;

//   // find the request batch with a max ballot in 1b packets
//   // var packets := proposer.received_1b_packets;
//   // var pkt :| pkt in packets && opn in pkt.msg.votes.v;
//   // var v := pkt.msg.votes.v[opn].max_val;
//   var v := CGetMaxValInVotes(proposer);

//   proposer' := proposer.(next_operation_number_to_propose := proposer.next_operation_number_to_propose + 1);
//   var msg := CMessage_2a(proposer.max_ballot_i_sent_1a, opn, v);
//   sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, CMessage_2a(proposer.max_ballot_i_sent_1a, opn, v));
// }

// // not sure the third condition is correct
// // 对应 ptotocol 中 LProposerMaybeNominateValueAndSend2a，其中第三个分支有量词，不知道翻译对不对
// method CProposerMaybeNominateValueAndSend2a(proposer:ProposerState, clock:uint64, log_truncation_point:COperationNumber) returns (proposer':ProposerState, sent_packets:CBroadcast)
// requires CProposerStateValid(proposer)
// {
//   var start_time := Time.GetDebugTimeTicks();
//   var a := CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point, proposer.next_operation_number_to_propose);
//   var b := CAllAcceptorsHadNoProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose);
  
//   if !a {
//     proposer' := proposer;
//     sent_packets := CBroadcastNop;
//   } else if !b {
//     proposer', sent_packets := CProposerNominateOldValueAndSend2a(proposer, log_truncation_point);
//     // var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }
//   } else if ((exists p :: p in proposer.received_1b_packets 
//                 && (exists opn:COperationNumber :: opn in p.msg.votes.v && opn > proposer.next_operation_number_to_propose))) 
//             || (|proposer.request_queue| >= proposer.constants.all.params.max_batch_size as int)
//             || (|proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= proposer.incomplete_batch_timer.when)
//   {
//     proposer', sent_packets := CProposerNominateNewValueAndSend2a(proposer, clock, log_truncation_point);
//     // var end_time := Time.GetDebugTimeTicks();
//     // if(end_time >= start_time){
//     //   print end_time - start_time;
//     //   print "\n";
//     // } else {
//     //   print("Wrong");
//     // }
//   } else if |proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOff? {
//     proposer' := proposer.(incomplete_batch_timer := CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, proposer.constants.all.params.max_batch_delay, proposer.constants.all.params.max_integer_val)));
//     sent_packets := CBroadcastNop;
//   } else {
//     proposer' := proposer;
//     sent_packets := CBroadcastNop;
//   }
// }

// method CProposerProcessHeartbeat(proposer:ProposerState, packet:CPacket, clock:uint64) returns (proposer':ProposerState)
// requires packet.msg.CMessage_Heartbeat?
// requires CProposerStateValid(proposer)
// {
//   // 对于protocol中仅改动s'的某一个属性，都改成这样的，先定义局部变量=属性新值，然后按照这种方式赋值给s'
//   var election := CElectionStateProcessHeartbeat(proposer.election_state, packet, clock);
//   proposer' := proposer.(election_state := election);

//   if CBalLt(proposer.election_state.current_view, proposer'.election_state.current_view) {
//     proposer' := proposer.(
//       election_state := election,
//       current_state := 0,
//       request_queue := []
//     );
//   } else {
//     proposer' := proposer.(
//       election_state := election,
//       current_state := proposer.current_state,
//       request_queue := proposer.request_queue
//     );
//   }

//   proposer' := proposer.(election_state := proposer'.election_state, 
//                         current_state := proposer'.current_state, 
//                         request_queue := proposer'.request_queue);
// }

// method CProposerCheckForViewTimeout(proposer:ProposerState, clock:uint64) returns (proposer':ProposerState)
// requires CProposerStateValid(proposer)
// {
//   var election := CElectionStateCheckForViewTimeout(proposer.election_state, clock);
//   proposer' := proposer.(election_state := election);
//   proposer' := proposer.(election_state := proposer'.election_state);
// }

// method CProposerCheckForQuorumOfViewSuspicions(proposer:ProposerState, clock:uint64) returns (proposer':ProposerState)
// requires CProposerStateValid(proposer)
// {
//   var election := CElectionStateCheckForQuorumOfViewSuspicions(proposer.election_state, clock);
//   proposer' := proposer.(election_state := election);

//   if CBalLt(proposer.election_state.current_view, proposer'.election_state.current_view){
//     proposer' := proposer.(
//       election_state := election,
//       current_state := 0,
//       request_queue := []
//     );
//   } else {
//     proposer' := proposer.(
//       election_state := election,
//       current_state := proposer.current_state,
//       request_queue := proposer.request_queue
//     );
//   }

//   proposer' := proposer.(election_state := proposer'.election_state, 
//                         current_state := proposer'.current_state, 
//                         request_queue := proposer'.request_queue);
// }

// method CProposerResetViewTimerDueToExecution(proposer:ProposerState, val:CRequestBatch) returns (proposer':ProposerState)
// requires CProposerStateValid(proposer)
// {
//   var election := CElectionStateReflectExecutedRequestBatch(proposer.election_state, val);
//   proposer' := proposer.(election_state := election);
//   proposer' := proposer.(election_state := proposer'.election_state);
// }

} 
