include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Constants.i.dfy"
include "Broadcast.i.dfy"
include "Election.i.dfy"
include "Acceptor.i.dfy"

module Impl_LiveRSL__Proposer_i {
 	import opened Impl_LiveRSL__Configuration_i
	import opened Impl_LiveRSL__Environment_i
	import opened Impl_LiveRSL__Constants_i
	import opened Impl_LiveRSL__Broadcast_i
	import opened Impl_LiveRSL__Acceptor_i
	import opened Impl_LiveRSL__Election_i
	import opened Impl_LiveRSL__Types_i
	import opened Impl_LiveRSL__Message_i
	import opened ToBeFilled
	import opened ToBeFilled

	datatype CIncompleteBatchTimer = 
	CIncompleteBatchTimerOn
	(
		when : int
	)
	|
	CIncompleteBatchTimerOff
	(
		
	)

	predicate CIncompleteBatchTimerIsValid(
		s : CIncompleteBatchTimer)
		
	{
		match s
			case CIncompleteBatchTimerOn(when) => CIncompleteBatchTimerIsAbstractable(s)
			case CIncompleteBatchTimerOff() => CIncompleteBatchTimerIsAbstractable(s)

	}

	predicate CIncompleteBatchTimerIsAbstractable(
		s : CIncompleteBatchTimer)
		
	{
		match s
			case CIncompleteBatchTimerOn(when) => true
			case CIncompleteBatchTimerOff() => true

	}

	function AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(
		s : CIncompleteBatchTimer) : IncompleteBatchTimer
		requires CIncompleteBatchTimerIsAbstractable(s)
	{
		match s
			case CIncompleteBatchTimerOn(when) => IncompleteBatchTimerOn(s.when)
			case CIncompleteBatchTimerOff() => IncompleteBatchTimerOff()

	}

	datatype CProposer = 
	CProposer
	(
		constants : CReplicaConstants ,
		current_state : int ,
		request_queue : seq<CRequest> ,
		max_ballot_i_sent_1a : CBallot ,
		next_operation_number_to_propose : int ,
		received_1b_packets : set<CPacket> ,
		highest_seqno_requested_by_client_this_view : map<EndPoint, int> ,
		incomplete_batch_timer : CIncompleteBatchTimer ,
		election_state : CElectionState
	)

	predicate CProposerIsValid(
		s : CProposer)
		
	{
		CProposerIsAbstractable(s)
		&&
		CReplicaConstantsIsValid(s.constants)
		&&
		(forall i :: i in s.request_queue ==> i.CRequest? && CRequestIsValid(i))
		&&
		CBallotIsValid(s.max_ballot_i_sent_1a)
		&&
		(forall i :: i in s.received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
		&&
		(forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsValid(i))
		&&
		CIncompleteBatchTimerIsValid(s.incomplete_batch_timer)
		&&
		CElectionStateIsValid(s.election_state)
	}

	predicate CProposerIsAbstractable(
		s : CProposer)
		
	{
		CReplicaConstantsIsAbstractable(s.constants)
		&&
		(forall i :: i in s.request_queue ==> i.CRequest? && CRequestIsAbstractable(i))
		&&
		CBallotIsAbstractable(s.max_ballot_i_sent_1a)
		&&
		(forall i :: i in s.received_1b_packets ==> i.CPacket? && CPacketIsAbstractable(i))
		&&
		(forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsAbstractable(i))
		&&
		CIncompleteBatchTimerIsAbstractable(s.incomplete_batch_timer)
		&&
		CElectionStateIsAbstractable(s.election_state)
	}

	function AbstractifyCProposerToLProposer(
		s : CProposer) : LProposer
		requires CProposerIsAbstractable(s)
	{
		LProposer(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.current_state, AbstractifySeq(s.request_queue, AbstractifyCRequestToRequest), AbstractifyCBallotToBallot(s.max_ballot_i_sent_1a), s.next_operation_number_to_propose, AbstractifySet(s.received_1b_packets, AbstractifyCPacketToRslPacket), AbstractifyMap(s.highest_seqno_requested_by_client_this_view, AbstractifyEndPointToNodeIdentity, NoChange, AbstractifyNodeIdentityToEndPoint), AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(s.incomplete_batch_timer), AbstractifyCElectionStateToElectionState(s.election_state))
	}

	function method CIsAfterLogTruncationPoint(
		opn : COperationNumber ,
		received_1b_packets : set<CPacket>) : bool
		requires COperationNumberIsValid(opn)
		requires (forall i :: i in received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
		ensures var bc := CIsAfterLogTruncationPoint(opn, received_1b_packets); var bl := LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket)); (bl) == (bc)
	{
		(forall p :: p in received_1b_packets && p.msg.CMessage_1b? ==> p.msg.log_truncation_point <= opn)
	}

	function method CSetOfMessage1b(
		S : set<CPacket>) : bool
		requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
		ensures var bc := CSetOfMessage1b(S); var bl := LSetOfMessage1b(AbstractifySet(S, AbstractifyCPacketToRslPacket)); (bl) == (bc)
	{
		forall p :: p in S ==> p.msg.CMessage_1b?
	}

	function method CSetOfMessage1bAboutBallot(
		S : set<CPacket> ,
		b : CBallot) : bool
		requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
		requires CBallotIsValid(b)
		ensures var bc := CSetOfMessage1bAboutBallot(S, b); var bl := LSetOfMessage1bAboutBallot(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCBallotToBallot(b)); (bl) == (bc)
	{

		&&
		CSetOfMessage1b(S)
		&&
		(forall p :: p in S ==> p.msg.bal_1b == b)
	}

	function method CAllAcceptorsHadNoProposal(
		S : set<CPacket> ,
		opn : COperationNumber) : bool
		requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
		ensures var bc := CAllAcceptorsHadNoProposal(S, opn); var bl := LAllAcceptorsHadNoProposal(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); (bl) == (bc)
	{
		forall p :: p in S ==> !(opn in p.msg.votes)
	}

	function method CExistVotesHasProposalLargeThanOpn(
		p : CPacket ,
		op : COperationNumber) : bool
		requires CPacketIsValid(p)
		requires COperationNumberIsValid(op)
		requires p.msg.CMessage_1b?
		ensures var bc := CExistVotesHasProposalLargeThanOpn(p, op); var bl := LExistVotesHasProposalLargeThanOpn(AbstractifyCPacketToRslPacket(p), AbstractifyCOperationNumberToOperationNumber(op)); (bl) == (bc)
	{
		exists opn :: opn in p.msg.votes && opn > op
	}

	function method CExistsAcceptorHasProposalLargeThanOpn(
		S : set<CPacket> ,
		op : COperationNumber) : bool
		requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
		requires COperationNumberIsValid(op)
		requires CSetOfMessage1b(S)
		ensures var bc := CExistsAcceptorHasProposalLargeThanOpn(S, op); var bl := LExistsAcceptorHasProposalLargeThanOpn(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(op)); (bl) == (bc)
	{
		exists p :: p in S && CExistVotesHasProposalLargeThanOpn(p, op)
	}

	function method Cmax_balInS(
		c : CBallot ,
		S : set<CPacket> ,
		opn : COperationNumber) : bool
		requires CBallotIsValid(c)
		requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
		ensures var bc := Cmax_balInS(c, S, opn); var bl := Lmax_balInS(AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); (bl) == (bc)
	{
		forall p :: p in S && opn in p.msg.votes ==> CBalLeq(p.msg.votes[opn].max_value_bal, c)
	}

	function method CExistsBallotInS(
		v : CRequestBatch ,
		c : CBallot ,
		S : set<CPacket> ,
		opn : COperationNumber) : bool
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(c)
		requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
		ensures var bc := CExistsBallotInS(v, c, S, opn); var bl := LExistsBallotInS(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); (bl) == (bc)
	{
		exists p ::  && p in S && opn in p.msg.votes && p.msg.votes[opn].max_value_bal == c && p.msg.votes[opn].max_val == v
	}

	function method CValIsHighestNumberedProposalAtBallot(
		v : CRequestBatch ,
		c : CBallot ,
		S : set<CPacket> ,
		opn : COperationNumber) : bool
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(c)
		requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
		ensures var bc := CValIsHighestNumberedProposalAtBallot(v, c, S, opn); var bl := LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); (bl) == (bc)
	{

		&&
		Cmax_balInS(c, S, opn)
		&&
		CExistsBallotInS(v, c, S, opn)
	}

	function method CValIsHighestNumberedProposal(
		v : CRequestBatch ,
		S : set<CPacket> ,
		opn : COperationNumber) : bool
		requires CRequestBatchIsValid(v)
		requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
		ensures var bc := CValIsHighestNumberedProposal(v, S, opn); var bl := LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); (bl) == (bc)
	{
		exists c :: CValIsHighestNumberedProposalAtBallot(v, c, S, opn)
	}

	function method CProposerCanNominateUsingOperationNumber(
		s : CProposer ,
		log_truncation_point : COperationNumber ,
		opn : COperationNumber) : bool
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		requires COperationNumberIsValid(opn)
		ensures var bc := CProposerCanNominateUsingOperationNumber(s, log_truncation_point, opn); var bl := LProposerCanNominateUsingOperationNumber(AbstractifyCProposerToLProposer(s), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCOperationNumberToOperationNumber(opn)); (bl) == (bc)
	{

		&&
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

	function method CProposerInit(
		c : CReplicaConstants) : CProposer
		requires CWellFormedLConfiguration(c.all.config)
		requires CReplicaConstantsIsValid(c)
		ensures var s := CProposerInit(c); CProposerIsValid(s) && LProposerInit(AbstractifyCProposerToLProposer(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		CProposer(constants := c, current_state := 0, election_state := CElectionStateInit(c), highest_seqno_requested_by_client_this_view := map[], incomplete_batch_timer := CIncompleteBatchTimerOff(), max_ballot_i_sent_1a := CBallot(0, c.my_index), next_operation_number_to_propose := 0, received_1b_packets := {}, request_queue := [])
	}

	function method CProposerProcessRequest(
		s : CProposer ,
		packet : CPacket) : CProposer
		requires CProposerIsValid(s)
		requires CPacketIsValid(packet)
		requires packet.msg.CMessage_Request?
		ensures var s' := CProposerProcessRequest(s, packet); CProposerIsValid(s') && LProposerProcessRequest(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(packet))
	{
		var val := CRequest(packet.src, packet.msg.seqno_req, packet.msg.val); 
		if  && s.current_state != 0 && ( || val.client !in s.highest_seqno_requested_by_client_this_view || val.seqno > s.highest_seqno_requested_by_client_this_view[val.client])
		then 
			s.(
				election_state := CElectionStateReflectReceivedRequest(s.election_state, val),
				request_queue := s.request_queue + [val],
				highest_seqno_requested_by_client_this_view := s.highest_seqno_requested_by_client_this_view[val.client := val.seqno]
			)
		else 
			s.(
				election_state := CElectionStateReflectReceivedRequest(s.election_state, val)
			)
	}

	function method CProposerMaybeEnterNewViewAndSend1a(
		s : CProposer) : (CProposer, CBroadcast)
		requires CProposerIsValid(s)
		ensures var (s', broadcast_sent_packets) := CProposerMaybeEnterNewViewAndSend1a(s); CProposerIsValid(s') && (forall i :: i in broadcast_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LProposerMaybeEnterNewViewAndSend1a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCBroadcastToRlsPacketSeq(broadcast_sent_packets))
	{
		if  && s.election_state.current_view.proposer_id == s.constants.my_index && CBalLt(s.max_ballot_i_sent_1a, s.election_state.current_view)
		then 
			(
				s.(
					current_state := 1,
					max_ballot_i_sent_1a := s.election_state.current_view,
					received_1b_packets := {},
					highest_seqno_requested_by_client_this_view := map[],
					request_queue := s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch
				),
				BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1a(s.election_state.current_view))
			)
		else 
			(
				s,
				CBroadcastNop
			)
	}

	function method CProposerProcess1b(
		s : CProposer ,
		p : CPacket) : CProposer
		requires CProposerIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_1b?
		requires p.src in s.constants.all.config.replica_ids
		requires p.msg.bal_1b == s.max_ballot_i_sent_1a
		requires s.current_state == 1
		requires forall other_packet :: other_packet in s.received_1b_packets ==> other_packet.src != p.src
		ensures var s' := CProposerProcess1b(s, p); CProposerIsValid(s') && LProposerProcess1b(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p))
	{
		s.(
			received_1b_packets := s.received_1b_packets + {p}
		)
	}

	function method CProposerMaybeEnterPhase2(
		s : CProposer ,
		log_truncation_point : COperationNumber) : (CProposer, CBroadcast)
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		ensures var (s', broadcast_sent_packets) := CProposerMaybeEnterPhase2(s, log_truncation_point); CProposerIsValid(s') && (forall i :: i in broadcast_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LProposerMaybeEnterPhase2(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(broadcast_sent_packets))
	{
		if  && |s.received_1b_packets| >= CMinQuorumSize(s.constants.all.config) && CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) && s.current_state == 1
		then 
			(
				s.(
					current_state := 2,
					next_operation_number_to_propose := log_truncation_point
				),
				BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_StartingPhase2(s.max_ballot_i_sent_1a, log_truncation_point))
			)
		else 
			(
				s,
				CBroadcastNop
			)
	}

	function method CProposerNominateNewValueAndSend2a(
		s : CProposer ,
		clock : int ,
		log_truncation_point : COperationNumber) : (CProposer, CBroadcast)
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
		requires CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
		ensures var (s', broadcast_sent_packets) := CProposerNominateNewValueAndSend2a(s, clock, log_truncation_point); CProposerIsValid(s') && (forall i :: i in broadcast_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LProposerNominateNewValueAndSend2a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(broadcast_sent_packets))
	{
		var batchSize := if |s.request_queue| <= s.constants.all.params.max_batch_size || s.constants.all.params.max_batch_size < 0 then |s.request_queue| else s.constants.all.params.max_batch_size; 
		var v := s.request_queue[..batchSize]; 
		var opn := s.next_operation_number_to_propose; 
		(
			s.(
				request_queue := s.request_queue[batchSize..],
				next_operation_number_to_propose := s.next_operation_number_to_propose + 1,
				incomplete_batch_timer := if |s.request_queue| > batchSize then CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)) else CIncompleteBatchTimerOff()
			),
			BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2a(s.max_ballot_i_sent_1a, opn, v))
		)
	}

	function method CProposerNominateOldValueAndSend2a(
		s : CProposer ,
		log_truncation_point : COperationNumber) : (CProposer, CBroadcast)
		requires CProposerIsValid(s)
		requires COperationNumberIsValid(log_truncation_point)
		requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
		requires !CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
		ensures var (s', broadcast_sent_packets) := CProposerNominateOldValueAndSend2a(s, log_truncation_point); CProposerIsValid(s') && (forall i :: i in broadcast_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(broadcast_sent_packets))
	{
		var opn := s.next_operation_number_to_propose; 
		.(
			
		)
	}

	function method CProposerMaybeNominateValueAndSend2a(
		s : CProposer ,
		clock : int ,
		log_truncation_point : int) : (CProposer, CBroadcast)
		requires CProposerIsValid(s)
		ensures var (s', broadcast_sent_packets) := CProposerMaybeNominateValueAndSend2a(s, clock, log_truncation_point); CProposerIsValid(s') && (forall i :: i in broadcast_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock, log_truncation_point, AbstractifyCBroadcastToRlsPacketSeq(broadcast_sent_packets))
	{
		if !CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
		then 
			(
				s,
				CBroadcastNop
			)
		else 
			if !CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
			then 
				var (t0_0, t1_0) := CProposerNominateOldValueAndSend2a(s, log_truncation_point); 
				(
					t0_0,
					t1_0
				)
			else 
				if CExistsAcceptorHasProposalLargeThanOpn(s.received_1b_packets, s.next_operation_number_to_propose) || |s.request_queue| >= s.constants.all.params.max_batch_size || (|s.request_queue| > 0 && s.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= s.incomplete_batch_timer.when)
				then 
					var (t0_0, t1_0) := CProposerNominateNewValueAndSend2a(s, clock, log_truncation_point); 
					(
						t0_0,
						t1_0
					)
				else 
					if |s.request_queue| > 0 && s.incomplete_batch_timer.CIncompleteBatchTimerOff?
					then 
						(
							s.(
								incomplete_batch_timer := CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val))
							),
							CBroadcastNop
						)
					else 
						(
							s,
							CBroadcastNop
						)
	}

	function method CProposerProcessHeartbeat(
		s : CProposer ,
		p : CPacket ,
		clock : int) : CProposer
		requires CProposerIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_Heartbeat?
		ensures var s' := CProposerProcessHeartbeat(s, p, clock); CProposerIsValid(s') && LProposerProcessHeartbeat(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p), clock)
	{
		if CBalLt(s.election_state.current_view, s'.election_state.current_view)
		then 
			s.(
				election_state := CElectionStateProcessHeartbeat(s.election_state, p, clock),
				current_state := 0,
				request_queue := []
			)
		else 
			s.(
				election_state := CElectionStateProcessHeartbeat(s.election_state, p, clock),
				current_state := s.current_state,
				request_queue := s.request_queue
			)
	}

	function method CProposerCheckForViewTimeout(
		s : CProposer ,
		clock : int) : CProposer
		requires CProposerIsValid(s)
		ensures var s' := CProposerCheckForViewTimeout(s, clock); CProposerIsValid(s') && LProposerCheckForViewTimeout(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	{
		s.(
			election_state := CElectionStateCheckForViewTimeout(s.election_state, clock)
		)
	}

	function method CProposerCheckForQuorumOfViewSuspicions(
		s : CProposer ,
		clock : int) : CProposer
		requires CProposerIsValid(s)
		ensures var s' := CProposerCheckForQuorumOfViewSuspicions(s, clock); CProposerIsValid(s') && LProposerCheckForQuorumOfViewSuspicions(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	{
		if CBalLt(s.election_state.current_view, s'.election_state.current_view)
		then 
			s.(
				election_state := CElectionStateCheckForQuorumOfViewSuspicions(s.election_state, clock),
				current_state := 0,
				request_queue := []
			)
		else 
			s.(
				election_state := CElectionStateCheckForQuorumOfViewSuspicions(s.election_state, clock),
				current_state := s.current_state,
				request_queue := s.request_queue
			)
	}

	function method CProposerResetViewTimerDueToExecution(
		s : CProposer ,
		val : CRequestBatch) : CProposer
		requires CProposerIsValid(s)
		requires CRequestBatchIsValid(val)
		ensures var s' := CProposerResetViewTimerDueToExecution(s, val); CProposerIsValid(s') && LProposerResetViewTimerDueToExecution(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCRequestBatchToRequestBatch(val))
	{
		s.(
			election_state := CElectionStateReflectExecutedRequestBatch(s.election_state, val)
		)
	}
 
}
