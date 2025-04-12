

type OperationNumber = int


datatype Ballot = 
Ballot(
	seqno: int, 
	proposer_id: int
)


datatype Request = 
Request(
	client: NodeIdentity, 
	seqno: int, 
	request: AppMessage
)


datatype Reply = 
Reply(
	client: NodeIdentity, 
	seqno: int, 
	reply: AppMessage
)

type RequestBatch = seq<Request>

type ReplyCache = map<NodeIdentity, Reply>


datatype Vote = 
Vote(
	max_value_bal: Ballot, 
	max_val: RequestBatch
)

type Votes = map<OperationNumber, Vote>


datatype LearnerTuple = 
LearnerTuple(
	received_2b_message_senders: set<NodeIdentity>, 
	candidate_learned_value: RequestBatch
)

type LearnerState = map<OperationNumber, LearnerTuple>


predicate BalLt(ba: STUB, bb: STUB) 
{
	(ba.seqno < bb.seqno) || (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
}


predicate BalLeq(ba: STUB, bb: STUB) 
{
	(ba.seqno < bb.seqno) || (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
}


datatype LConfiguration = 
LConfiguration(
	replica_ids: seq<NodeIdentity>
)


predicate LMinQuorumSize(c: STUB) 
{
	|c.replica_ids| / 2 + 1
}


predicate ReplicasDistinct(replica_ids: STUB, i: STUB, j: STUB) 
{
	0 <= i 
	&& 
	i < |replica_ids| 
	&& (
	replica_ids[i] == replica_ids[j] ==> i == j)
}


predicate ReplicasIsUnique(replica_ids: STUB) 
{
	(forall i, j :: 0 <= i && i < |replica_ids| && 0 <= j && j < |replica_ids| && (replica_ids[i] == replica_ids[j] ==> i == j))
}


predicate WellFormedLConfiguration(c: STUB) 
{
	|c.replica_ids| > 0 
	&& 
	(forall i, j :: ReplicasDistinct(c.replica_ids, i, j) && ReplicasIsUnique(c.replica_ids))
}


predicate IsReplicaIndex(idx: STUB, id: STUB, c: STUB) 
{
	0 <= idx 
	&& 
	idx < |c.replica_ids| 
	&& 
	c.replica_ids[idx] == id
}


predicate GetReplicaIndex(id: STUB, c: STUB) 
{
	FindIndexInSeq(c.replica_ids, id)
}


datatype LParameters = 
LParameters(
	max_log_length: int, 
	baseline_view_timeout_period: int, 
	heartbeat_period: int, 
	max_integer_val: UpperBound, 
	max_batch_size: int, 
	max_batch_delay: int
)


predicate WFLParameters(p: STUB) 
{
	p.max_log_length > 0 
	&& 
	p.baseline_view_timeout_period > 0 
	&& 
	p.heartbeat_period > 0 
	&& 
	(p.max_integer_val.UpperBoundFinite ==> p.max_integer_val.n > p.max_log_length) 
	&& 
	p.max_batch_size > 0 
	&& 
	p.max_batch_delay >= 0
}


datatype LConstants = 
LConstants(
	config: LConfiguration, 
	params: LParameters
)


datatype LReplicaConstants = 
LReplicaConstants(
	my_index: int, 
	all: LConstants
)


predicate LReplicaConstantsValid(c: STUB) 
{
	0 <= c.my_index 
	&& 
	c.my_index < |c.all.config.replica_ids|
}

type RslEnvironment = LEnvironment<NodeIdentity>

type RslPacket = LPacket<NodeIdentity>

type RslIo = LIoOp<NodeIdentity>


predicate LBroadcastToEveryone(c: STUB, myidx: STUB, m: STUB, sent_packets: STUB) 
{
	|sent_packets| == |c.replica_ids| 
	&& 
	0 <= myidx 
	&& 
	myidx <= |c.replica_ids| 
	&& 
	(forall idx :: 0 <= idx && (idx < |sent_packets| ==> sent_packets[idx] == STUB(c.replica_ids[idx], c.replica_ids[myidx + 1], m)))
}


datatype ClockReading = 
ClockReading(
	t: int
)


datatype LAcceptor = 
LAcceptor(
	constants: LReplicaConstants, 
	max_bal: Ballot, 
	votes: Votes, 
	last_checkpointed_operation: seq<OperationNumber>, 
	log_truncation_point: OperationNumber
)


predicate IsLogTruncationPointValid(log_truncation_point: STUB, last_checkpointed_operation: STUB, config: STUB) 
{
	IsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, LMinQuorumSize(config))
}


predicate RemoveVotesBeforeLogTruncationPoint(votes: STUB, votes_next: STUB, log_truncation_point: STUB) 
{
	(forall opn :: opn in votes_next ==> opn in votes && votes_next[opn] == votes[opn]) 
	&& 
	(forall opn :: opn < log_truncation_point ==> opn !in votes_next) 
	&& 
	(forall opn :: opn >= log_truncation_point ==> opn in votes_next) 
	&& 
	(forall opn :: opn in votes && (opn >= log_truncation_point ==> opn in votes_next && votes_next[opn] == votes[opn]))
}


predicate LAddVoteAndRemoveOldOnes(votes: STUB, votes_next: STUB, new_opn: STUB, new_vote: STUB, log_truncation_point: STUB) 
{
	(forall opn :: opn in (votes_next ==> opn >= log_truncation_point) && opn in (votes) || (opn == new_opn)) 
	&& 
	(forall opn :: opn >= log_truncation_point && (opn in (votes) || (opn == new_opn) ==> opn in votes')) 
	&& 
	(forall opn :: opn in votes_next ==> votes_next[opn] == if opn == new_opn then new_vote else votes[opn])
}


predicate LAcceptorInit(a: STUB, c: STUB) 
{
	a.constants == c 
	&& 
	a.max_bal == STUB(0, 0) 
	&& 
	a.votes == map[] 
	&& 
	|a.last_checkpointed_operation| == |c.all.config.replica_ids| 
	&& 
	(forall idx :: 0 <= idx && (idx < |a.last_checkpointed_operation| ==> a.last_checkpointed_operation[idx] == 0)) 
	&& 
	a.log_truncation_point == 0
}


predicate LAcceptorProcess1a(s: STUB, s_next: STUB, inp: STUB, sent_packets: STUB) 
{
	inp.msg.type.RslMessage_1a? 
	&& 
	var m := 
		inp.msg; 	
	if inp.src in s.constants.all.config.replica_ids && BalLt(s.max_bal, m.bal_1a) && LReplicaConstantsValid(s.constants) then 
		sent_packets == [STUB(inp.src, s.constants.all.config.replica_ids[s.constants.my_index], STUB("RslMessage_1b", m.bal_1a, s.log_truncation_point, s.votes))] 
		&& 
		s_next == s.(max_bal := m.bal_1a) 
	else 
		sent_packets == [] 
		&& 
		s_next == s
}


predicate LAcceptorProcess2a(s: STUB, s_next: STUB, inp: STUB, sent_packets: STUB) 
{
	inp.msg.type.RslMessage_2a? 
	&& 
	inp.src in s.constants.all.config.replica_ids 
	&& 
	BalLeq(s.max_bal, inp.msg.bal_2a) 
	&& 
	LeqUpperBound(inp.msg.opn_2a, s.constants.all.params.max_integer_val) 
	&& 
	var m := 
		inp.msg; 	
	var newLogTruncationPoint := 
		if m.opn_2a - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then 
			m.opn_2a - s.constants.all.params.max_log_length + 1 
		else 
			s.log_truncation_point; 	
	LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, STUB("RslMessage_2b", m.bal_2a, m.opn_2a, m.val_2a), sent_packets) 
	&& 
	s_next == s.(max_bal := m.bal_2a, log_truncation_point := newLogTruncationPoint, votes := if s.log_truncation_point <= m.opn_2a then LAddVoteAndRemoveOldOnes(s.votes, s_next.votes, m.opn_2a, STUB(m.bal_2a, m.val_2a), newLogTruncationPoint) else s.votes)
}


predicate LAcceptorProcessHeartbeat(s: STUB, s_next: STUB, inp: STUB) 
{
	inp.msg.type.RslMessage_Heartbeat? 
	&& 
	if inp.src in s.constants.all.config.replica_ids then 
		var sender_index := 
			GetReplicaIndex(inp.src, s.constants.all.config); 		
		if 0 <= sender_index && sender_index <= |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then 
			s_next == s.(last_checkpointed_operation := inp.msg.opn_ckpt) 
		else 
			s_next == s 
	else 
		s_next == s
}


predicate LAcceptorTruncateLog(s: STUB, s_next: STUB, opn: STUB) 
{
	if opn <= s.log_truncation_point then 
		s_next == s 
	else 
		RemoveVotesBeforeLogTruncationPoint(s.votes, s_next.votes, opn) 
		&& 
		s_next == s.(log_truncation_point := opn, votes := s_next.votes)
}


datatype LLearner = 
LLearner(
	constants: LReplicaConstants, 
	max_ballot_seen: Ballot, 
	unexecuted_learner_state: LearnerState
)


predicate LLearnerInit(l: STUB, c: STUB) 
{
	l.constants == c 
	&& 
	l.max_ballot_seen == STUB(0, 0) 
	&& 
	l.unexecuted_learner_state == map[]
}


predicate LLearnerProcess2b(s: STUB, s_next: STUB, packet: STUB) 
{
	packet.msg.type.RslMessage_2b? 
	&& 
	var m := 
		packet.msg; 	
	var opn := 
		m.opn_2b; 	
	if (packet.src !in s.constants.all.config.replica_ids) || (BalLt(m.bal_2b, s.max_ballot_seen)) then 
		s_next == s 
	else 
		if BalLt(s.max_ballot_seen, m.bal_2b) then 
			var tup_next := 
				STUB({packet.src}, m.val_2b); 			
			s_next == s.(max_ballot_seen := m.bal_2b, unexecuted_learner_state := tup_next) 
		else 
			if opn !in s.unexecuted_learner_state then 
				var tup_next := 
					STUB({packet.src}, m.val_2b); 				
				s_next == s.(unexecuted_learner_state := tup_next) 
			else 
				if packet.src in s.unexecuted_learner_state[opn].received_2b_message_senders then 
					s_next == s 
				else 
					var tup := 
						s.unexecuted_learner_state[opn]; 					
					var tup_next := 
						tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src}); 					
					s_next == s.(unexecuted_learner_state := tup_next)
}


predicate LLearnerForgetDecision(s: STUB, s_next: STUB, opn: STUB) 
{
	if opn in s.unexecuted_learner_state then 
		s_next == s.(unexecuted_learner_state := RemoveElt(s.unexecuted_learner_state, opn)) 
	else 
		s_next == s
}


datatype ElectionState = 
ElectionState(
	constants: LReplicaConstants, 
	current_view: Ballot, 
	current_view_suspectors: set<int>, 
	epoch_length: int, 
	requests_received_this_epoch: seq<Request>, 
	requests_received_prev_epochs: seq<Request>
)


predicate ComputeSuccessorView(b: STUB, c: STUB) 
{
	if b.proposer_id + 1 < |c.config.replica_ids| then 
		STUB(b.seqno, b.proposer_id + 1) 
	else 
		STUB(b.seqno + 1, 0)
}


predicate BoundRequestSequence(s: STUB, lengthBound: STUB) 
{
	if lengthBound.type.UpperBoundFinite? && 0 <= lengthBound.n && lengthBound.n < |s| then 
		s[0 .. lengthBound.n] 
	else 
		s
}


predicate RequestsMatch(r1: STUB, r2: STUB) 
{
	r1.type.Request? 
	&& 
	r2.type.Request? 
	&& 
	r1.client == r2.client 
	&& 
	r1.seqno == r2.seqno
}


predicate RequestSatisfiedBy(r1: STUB, r2: STUB) 
{
	r1.type.Request? 
	&& 
	r2.type.Request? 
	&& 
	r1.client == r2.client 
	&& 
	r1.seqno <= r2.seqno
}


predicate RemoveAllSatisfiedRequestsInSequence(s: STUB, r: STUB) 
{
	if |s| == 0 then 
		[] 
	else 
		if RequestSatisfiedBy(s[0], r) then 
			RemoveAllSatisfiedRequestsInSequence(s[1 .. |s|], r) 
		else 
			[s[0]] + RemoveAllSatisfiedRequestsInSequence(s[1 .. |s|], r)
}


predicate ElectionStateInit(es: STUB, c: STUB) 
{
	|c.all.config.replica_ids| > 0 
	&& 
	es.constants == c 
	&& 
	es.current_view == STUB(1, 0) 
	&& 
	es.current_view_suspectors == {} 
	&& 
	es.epoch_end_time == 0 
	&& 
	es.epoch_length == c.all.params.baseline_view_timeout_period 
	&& 
	es.requests_received_this_epoch == [] 
	&& 
	es.requests_received_prev_epochs == []
}


predicate ElectionStateProcessHeartbeat(es: STUB, es_next: STUB, p: STUB, clock: STUB) 
{
	p.msg.type.RslMessage_Heartbeat? 
	&& 
	if p.src !in es.constants.all.config.replica_ids then 
		es_next == es 
	else 
		var sender_index := 
			GetReplicaIndex(p.src, es.constants.all.config); 		
		if p.msg.bal_heartbeat == es.current_view && p.msg.suspicious then 
			es_next == es.(current_view_suspectors := es.current_view_suspectors + {sender_index}) 
		else 
			if BalLt(es.current_view, p.msg.bal_heartbeat) then 
				var new_epoch_length := 
					UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); 				
				es_next == es.(current_view := p.msg.bal_heartbeat, current_view_suspectors := if p.msg.suspicious then {sender_index} else {}, epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := []) 
			else 
				es_next == es
}


predicate ElectionStateCheckForViewTimeout(es: STUB, es_next: STUB, clock: STUB) 
{
	if clock < es.epoch_end_time then 
		es_next == es 
	else 
		if |es.requests_received_prev_epochs| == 0 then 
			var new_epoch_length := 
				es.constants.all.params.baseline_view_timeout_period; 			
			es_next == es.(epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := es.requests_received_this_epoch, requests_received_this_epoch := []) 
		else 
			es_next == es.(current_view_suspectors := es.current_view_suspectors + {es.constants.my_index}, epoch_end_time := UpperBoundedAddition(clock, es.epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := [])
}


predicate ElectionStateCheckForQuorumOfViewSuspicions(es: STUB, es_next: STUB, clock: STUB) 
{
	if (|es.current_view_suspectors| < LMinQuorumSize(es.constants.all.config)) || (!(LtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val))) then 
		es_next == es 
	else 
		var new_epoch_length := 
			UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); 		
		es_next == es.(current_view := ComputeSuccessorView(es.current_view, es.constants.all), current_view_suspectors := {}, epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := [])
}


predicate ElectionStateReflectReceivedRequest(es: STUB, es_next: STUB, req: STUB) 
{
	if (exists earlier_req :: ((earlier_req in es.requests_received_prev_epochs) || (earlier_req in es.requests_received_this_epoch)) && RequestsMatch(earlier_req, req)) then 
		es_next == es 
	else 
		es_next == es.(requests_received_this_epoch := BoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val))
}


predicate RemoveExecutedRequestBatch(reqs: STUB, batch: STUB) 
{
	if |batch| == 0 then 
		reqs 
	else 
		RemoveExecutedRequestBatch(RemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), batch[1 .. |batch|])
}


predicate ElectionStateReflectExecutedRequestBatch(es: STUB, es_next: STUB, batch: STUB) 
{
	es_next == es.(requests_received_prev_epochs := RemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch), requests_received_this_epoch := RemoveExecutedRequestBatch(es.requests_received_this_epoch, batch))
}


datatype LProposer = 
LProposer(
	constants: LReplicaConstants, 
	current_state: int, 
	request_queue: seq<Request>, 
	max_ballot_i_sent_1a: Ballot, 
	next_operation_number_to_propose: int, 
	received_1b_packets: set<RslPacket>, 
	election_state: ElectionState
)


predicate LIsAfterLogTruncationPoint(opn: STUB, received_1b_packets: STUB) 
{
	(forall p :: p in received_1b_packets && (p.msg.type.RslMessage_1b? ==> p.msg.log_truncation_point <= opn))
}


predicate LSetOfMessage1b(S: STUB) 
{
	(forall p :: p in S ==> p.msg.type.RslMessage_1b?)
}


predicate LSetOfMessage1bAboutBallot(S: STUB, b: STUB) 
{
	LSetOfMessage1b(S) 
	&& 
	(forall p :: p in S ==> p.msg.bal_1b == b)
}


predicate LExistVotesHasProposalLargeThanOpn(p: STUB, op: STUB) 
{
	p.msg.type.RslMessage_1b? 
	&& 
	(exists opn :: opn in p.msg.votes && opn > op)
}


predicate LExistsAcceptorHasProposalLargeThanOpn(S: STUB, op: STUB) 
{
	LSetOfMessage1b(S) 
	&& 
	(exists p :: p in S && LExistVotesHasProposalLargeThanOpn(p, op))
}


predicate LAllAcceptorsHadNoProposal(S: STUB, opn: STUB) 
{
	LSetOfMessage1b(S) 
	&& 
	(forall p :: p in S ==> opn !in p.msg.votes)
}


predicate Lmax_balInS(c: STUB, S: STUB, opn: STUB) 
{
	LSetOfMessage1b(S) 
	&& 
	(forall p :: p in S && opn in p.msg.votes ==> BalLeq(p.msg.votes[opn].max_value_bal, c))
}


predicate LExistsBallotInS(v: STUB, c: STUB, S: STUB, opn: STUB) 
{
	LSetOfMessage1b(S) 
	&& 
	(exists p :: p in S && opn in p.msg.votes && p.msg.votes[opn].max_value_bal == c && p.msg.votes[opn].max_val == v)
}


predicate LValIsHighestNumberedProposalAtBallot(v: STUB, c: STUB, S: STUB, opn: STUB) 
{
	Lmax_balInS(c, S, opn) 
	&& 
	LExistsBallotInS(v, c, S, opn)
}


predicate LValIsHighestNumberedProposal(v: STUB, S: STUB, opn: STUB) 
{
	LSetOfMessage1b(S) 
	&& 
	(exists c :: LValIsHighestNumberedProposalAtBallot(v, c, S, opn))
}


predicate LProposerCanNominateUsingOperationNumber(s: STUB, log_truncation_point: STUB, opn: STUB) 
{
	s.election_state.current_view == s.max_ballot_i_sent_1a 
	&& 
	s.current_state == 2 
	&& 
	|s.received_1b_packets| >= LMinQuorumSize(s.constants.all.config) 
	&& 
	LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) 
	&& 
	LIsAfterLogTruncationPoint(opn, s.received_1b_packets) 
	&& 
	opn < UpperBoundedAddition(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val) 
	&& 
	opn >= 0 
	&& 
	LtUpperBound(opn, s.constants.all.params.max_integer_val)
}


predicate LProposerInit(s: STUB, c: STUB) 
{
	WellFormedLConfiguration(c.all.config) 
	&& 
	s.constants == c 
	&& 
	s.current_state == 0 
	&& 
	s.request_queue == [] 
	&& 
	s.max_ballot_i_sent_1a == STUB(0, c.my_index) 
	&& 
	s.next_operation_number_to_propose == 0 
	&& 
	s.received_1b_packets == {} 
	&& 
	s.highest_seqno_requested_by_client_this_view == map[] 
	&& 
	ElectionStateInit(s.election_state, c) 
	&& 
	s.incomplete_batch_timer.type.IncompleteBatchTimerOff?
}


predicate LProposerProcessRequest(s: STUB, s_next: STUB, packet: STUB) 
{
	packet.msg.type.RslMessage_Request? 
	&& 
	var val := 
		STUB(packet.src, packet.msg.seqno_req, packet.msg.val); 	
	ElectionStateReflectReceivedRequest(s.election_state, s_next.election_state, val) 
	&& 
	if s.current_state != 0 && val.client !in (s.highest_seqno_requested_by_client_this_view) || (val.seqno > s.highest_seqno_requested_by_client_this_view[val.client]) then 
		s_next == s.(election_state := s_next.election_state, request_queue := s.request_queue + [val], highest_seqno_requested_by_client_this_view := val.seqno) 
	else 
		s_next == s.(election_state := s_next.election_state)
}


predicate LProposerMaybeEnterNewViewAndSend1a(s: STUB, s_next: STUB, sent_packets: STUB) 
{
	if s.election_state.current_view.proposer_id == s.constants.my_index && BalLt(s.max_ballot_i_sent_1a, s.election_state.current_view) then 
		s_next == s.(current_state := 1, max_ballot_i_sent_1a := s.election_state.current_view, received_1b_packets := {}, highest_seqno_requested_by_client_this_view := map[], request_queue := s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch) 
		&& 
		LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, STUB("RslMessage_1a", s.election_state.current_view), sent_packets) 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LProposerProcess1b(s: STUB, s_next: STUB, p: STUB) 
{
	p.msg.type.RslMessage_1b? 
	&& 
	p.src in s.constants.all.config.replica_ids 
	&& 
	p.msg.bal_1b == s.max_ballot_i_sent_1a 
	&& 
	s.current_state == 1 
	&& 
	(forall other_packet :: other_packet in s.received_1b_packets ==> other_packet.src != p.src) 
	&& 
	s_next == s.(received_1b_packets := s.received_1b_packets + {p})
}


predicate LProposerMaybeEnterPhase2(s: STUB, s_next: STUB, log_truncation_point: STUB, sent_packets: STUB) 
{
	if |s.received_1b_packets| >= LMinQuorumSize(s.constants.all.config) && LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) && s.current_state == 1 then 
		s_next == s.(current_state := 2, next_operation_number_to_propose := log_truncation_point) 
		&& 
		LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, STUB("RslMessage_StartingPhase2", s.max_ballot_i_sent_1a, log_truncation_point), sent_packets) 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LProposerNominateNewValueAndSend2a(s: STUB, s_next: STUB, clock: STUB, log_truncation_point: STUB, sent_packets: STUB) 
{
	LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose) 
	&& 
	LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose) 
	&& 
	var batchSize := 
		if (|s.request_queue| <= s.constants.all.params.max_batch_size) || (s.constants.all.params.max_batch_size < 0) then 
			|s.request_queue| 
		else 
			s.constants.all.params.max_batch_size; 	
	var v := 
		s.request_queue[0 .. batchSize]; 	
	var opn := 
		s.next_operation_number_to_propose; 	
	s_next == s.(request_queue := s.request_queue[batchSize .. |s.request_queue|], next_operation_number_to_propose := s.next_operation_number_to_propose + 1, incomplete_batch_timer := if |s.request_queue| > batchSize then STUB("IncompleteBatchTimerOn", UpperBoundedAddition(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)) else STUB("IncompleteBatchTimerOff")) 
	&& 
	LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, STUB("RslMessage_2a", s.max_ballot_i_sent_1a, opn, v), sent_packets)
}


predicate LProposerNominateOldValueAndSend2a(s: STUB, s_next: STUB, log_truncation_point: STUB, sent_packets: STUB) 
{
	LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose) 
	&& 
	!(LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose) && var opn := s.next_operation_number_to_propose; (exists p :: p in s.received_1b_packets && opn in p.msg.votes && LValIsHighestNumberedProposal(p.msg.votes[opn].max_val, s.received_1b_packets, opn) && s_next == s.(next_operation_number_to_propose := s.next_operation_number_to_propose + 1) && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, STUB("RslMessage_2a", s.max_ballot_i_sent_1a, opn, p.msg.votes[opn].max_val), sent_packets)))
}


predicate LProposerMaybeNominateValueAndSend2a(s: STUB, s_next: STUB, clock: STUB, log_truncation_point: STUB, sent_packets: STUB) 
{
	if !(LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)) then 
		s_next == s 
		&& 
		sent_packets == [] 
	else 
		if !(LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)) then 
			LProposerNominateOldValueAndSend2a(s, s_next, log_truncation_point, sent_packets) 
		else 
			if ((LExistsAcceptorHasProposalLargeThanOpn(s.received_1b_packets, s.next_operation_number_to_propose)) || (|s.request_queue| >= s.constants.all.params.max_batch_size)) || (|s.request_queue| > 0 && s.incomplete_batch_timer.type.IncompleteBatchTimerOn? && clock >= s.incomplete_batch_timer.when) then 
				LProposerNominateNewValueAndSend2a(s, s_next, clock, log_truncation_point, sent_packets) 
			else 
				if |s.request_queue| > 0 && s.incomplete_batch_timer.type.IncompleteBatchTimerOff? then 
					s_next == s.(incomplete_batch_timer := STUB("IncompleteBatchTimerOn", UpperBoundedAddition(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val))) 
					&& 
					sent_packets == [] 
				else 
					s_next == s 
					&& 
					sent_packets == []
}


predicate LProposerProcessHeartbeat(s: STUB, s_next: STUB, p: STUB, clock: STUB) 
{
	p.msg.type.RslMessage_Heartbeat? 
	&& 
	ElectionStateProcessHeartbeat(s.election_state, s_next.election_state, p, clock) 
	&& 
	if BalLt(s.election_state.current_view, s_next.election_state.current_view) then 
		s_next.current_state == 0 
		&& 
		s_next.request_queue == [] 
	else 
		s_next.current_state == s.current_state 
		&& 
		s_next.request_queue == s.request_queue 
		&& 
		s_next == s.(election_state := s_next.election_state, current_state := s_next.current_state, request_queue := s_next.request_queue)
}


predicate LProposerCheckForViewTimeout(s: STUB, s_next: STUB, clock: STUB) 
{
	ElectionStateCheckForViewTimeout(s.election_state, s_next.election_state, clock) 
	&& 
	s_next == s.(election_state := s_next.election_state)
}


predicate LProposerCheckForQuorumOfViewSuspicions(s: STUB, s_next: STUB, clock: STUB) 
{
	ElectionStateCheckForQuorumOfViewSuspicions(s.election_state, s_next.election_state, clock) 
	&& 
	if BalLt(s.election_state.current_view, s_next.election_state.current_view) then 
		s_next.current_state == 0 
		&& 
		s_next.request_queue == [] 
	else 
		s_next.current_state == s.current_state 
		&& 
		s_next.request_queue == s.request_queue 
		&& 
		s_next == s.(election_state := s_next.election_state, current_state := s_next.current_state, request_queue := s_next.request_queue)
}


predicate LProposerResetViewTimerDueToExecution(s: STUB, s_next: STUB, val: STUB) 
{
	ElectionStateReflectExecutedRequestBatch(s.election_state, s_next.election_state, val) 
	&& 
	s_next == s.(election_state := s_next.election_state)
}


predicate HandleRequest(state: STUB, request: STUB) 
{
	var result := 
		AppHandleRequest(state, request.request); 	
	[result[1], STUB(request.client, request.seqno, result[2])]
}


predicate HandleRequestBatchHidden(state: STUB, batch: STUB) 
{
	if |batch| == 0 then 
		[state] 
	else 
		var result1 := 
			HandleRequestBatchHidden(state, batch[0 .. |batch| - 1]); 		
		[result1[1] + [result2[1]], result1[2] + [STUB(batch[|batch| - 1].client, batch[|batch| - 1].seqno, result2[2])]]
}


predicate HandleRequestBatch(state: STUB, batch: STUB) 
{
	HandleRequestBatchHidden(state, batch)
}


datatype LExecutor = 
LExecutor(
	constants: LReplicaConstants, 
	app: AppState, 
	ops_complete: int, 
	max_bal_reflected: Ballot, 
	next_op_to_execute: OutstandingOperation, 
	reply_cache: ReplyCache
)


predicate LExecutorInit(s: STUB, c: STUB) 
{
	s.constants == c 
	&& 
	s.app == 0 
	&& 
	s.ops_complete == 0 
	&& 
	s.max_bal_reflected == STUB(0, 0) 
	&& 
	s.next_op_to_execute == STUB("OutstandingOpKnown") 
	&& 
	s.reply_cache == map[]
}


predicate LExecutorGetDecision(s: STUB, s_next: STUB, bal: STUB, opn: STUB, v: STUB) 
{
	opn == s.ops_complete 
	&& 
	s.next_op_to_execute.type.OutstandingOpUnknown? 
	&& 
	s_next == s.(next_op_to_execute := STUB("OutstandingOpKnown", v, bal))
}


predicate GetPacketsFromReplies(me: STUB, requests: STUB, replies: STUB) 
{
	if |requests| == 0 then 
		[] 
	else 
		var p := 
			STUB(requests[0].client, me, STUB("RslMessage_Reply", requests[0].seqno, replies[0].reply)); 		
		[p] + GetPacketsFromReplies(me, requests[1 .. |requests|], replies[1 .. |replies|])
}


predicate UpdateNewCache(c: STUB, c_next: STUB, replies: STUB) 
{
	var nc := 
		LClientsInReplies(replies); 	
	(forall client :: client in (c_next ==> (client in c && c_next[client] == c[client]) || ((exists req_idx :: 0 <= req_idx && req_idx < |replies| && replies[req_idx].client == client && c_next[client] == replies[req_idx]))) && (forall client :: client in c_next ==> client in (c) || (client in nc && (forall client :: client in (c) || (client in nc ==> client in c_next && (forall client :: client in c_next ==> c_next[client] == if client in c then c[client] else nc[client]))))))
}


predicate LExecutorExecute(s: STUB, s_next: STUB, sent_packets: STUB) 
{
	s.next_op_to_execute.type.OutstandingOpKnown? 
	&& 
	LtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val) 
	&& 
	LReplicaConstantsValid(s.constants) 
	&& 
	var batch := 
		s.next_op_to_execute.value; 	
	s_next.constants == s.constants 
	&& 
	s_next.app == new_state 
	&& 
	s_next.ops_complete == s.ops_complete + 1 
	&& 
	s_next.max_bal_reflected == if BalLeq(s.max_bal_reflected, s.next_op_to_execute.ballot) then s.next_op_to_execute.ballot else s.max_bal_reflected && s_next.next_op_to_execute == STUB("OutstandingOpUnknown") && UpdateNewCache(s.reply_cache, s_next.reply_cache, replies) && sent_packets == GetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies)
}


predicate LExecutorProcessAppStateSupply(s: STUB, s_next: STUB, inp: STUB) 
{
	inp.msg.type.RslMessage_AppStateSupply? 
	&& 
	inp.src in s.constants.all.config.replica_ids 
	&& 
	inp.msg.opn_state_supply > s.ops_complete 
	&& 
	s_next == s.(app := inp.msg.app_state, ops_complete := inp.msg.opn_state_supply, max_bal_reflected := inp.msg.bal_state_supply, next_op_to_execute := STUB("OutstandingOpUnknown"), reply_cache := inp.msg.reply_cache)
}


predicate LExecutorProcessAppStateRequest(s: STUB, s_next: STUB, inp: STUB, sent_packets: STUB) 
{
	inp.msg.type.RslMessage_AppStateRequest? 
	&& 
	var m := 
		inp.msg; 	
	if inp.src in s.constants.all.config.replica_ids && BalLeq(s.max_bal_reflected, m.bal_state_req) && s.ops_complete >= m.opn_state_req && LReplicaConstantsValid(s.constants) then 
		s_next == s 
		&& 
		sent_packets == [STUB(inp.src, s.constants.all.config.replica_ids[s.constants.my_index], STUB("RslMessage_AppStateSupply", s.max_bal_reflected, s.ops_complete, s.app, s.reply_cache))] 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LExecutorProcessStartingPhase2(s: STUB, s_next: STUB, inp: STUB, sent_packets: STUB) 
{
	inp.msg.type.RslMessage_StartingPhase2? 
	&& 
	var m := 
		inp.msg; 	
	if inp.src in s.constants.all.config.replica_ids && m.logTruncationPoint_2 > s.ops_complete then 
		s_next == s 
		&& 
		LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, STUB("RslMessage_AppStateRequest", m.bal_2, m.logTruncationPoint_2), sent_packets) 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LExecutorProcessRequest(s: STUB, inp: STUB, sent_packets: STUB) 
{
	inp.msg.type.RslMessage_Request? 
	&& 
	inp.src in s.reply_cache && inp.msg.seqno_req <= s.reply_cache[inp.src].seqno && var r := s.reply_cache[inp.src]; if inp.msg.seqno_req == r.seqno && LReplicaConstantsValid(s.constants) then sent_packets == [STUB(r.client, s.constants.all.config.replica_ids[s.constants.my_index], STUB("RslMessage_Reply", r.seqno, r.reply))] else sent_packets == []
}


datatype LReplica = 
LReplica(
	constants: LReplicaConstants, 
	nextHeartbeatTime: int, 
	proposer: LProposer, 
	acceptor: LAcceptor, 
	learner: LLearner, 
	executor: LExecutor
)


predicate LReplicaInit(r: STUB, c: STUB) 
{
	WellFormedLConfiguration(c.all.config) 
	&& 
	r.constants == c 
	&& 
	r.nextHeartbeatTime == 0 
	&& 
	LProposerInit(r.proposer, c) 
	&& 
	LAcceptorInit(r.acceptor, c) 
	&& 
	LLearnerInit(r.learner, c) 
	&& 
	LExecutorInit(r.executor, c)
}


predicate LReplicaNextProcessInvalid(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_Invalid? 
	&& 
	s_next == s 
	&& 
	sent_packets == []
}


predicate LReplicaNextProcessRequest(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_Request? 
	&& 
	if received_packet.src in s.executor.reply_cache && received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno then 
		LExecutorProcessRequest(s.executor, received_packet, sent_packets) 
		&& 
		s_next == s 
	else 
		LProposerProcessRequest(s.proposer, s_next.proposer, received_packet) 
		&& 
		sent_packets == [] 
		&& 
		s_next == s.(proposer := s_next.proposer)
}


predicate LReplicaNextProcess1a(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_1a? 
	&& 
	LAcceptorProcess1a(s.acceptor, s_next.acceptor, received_packet, sent_packets) 
	&& 
	s_next == s.(acceptor := s_next.acceptor)
}


predicate LReplicaNextProcess1b(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_1b? 
	&& 
	var proposerConfig := 
		s.proposer.constants.all.config.replica_ids; 	
	if received_packet.src in proposerConfig && received_packet.msg.bal_1b == proposerBallot && proposerState == 1 && (forall other_packet :: other_packet in proposerReceived ==> other_packet.src != received_packet.src) then 
		LProposerProcess1b(s.proposer, s_next.proposer, received_packet) 
		&& 
		LAcceptorTruncateLog(s.acceptor, s_next.acceptor, received_packet.msg.log_truncation_point) 
		&& 
		sent_packets == [] 
		&& 
		s_next == s.(proposer := s_next.proposer, acceptor := s_next.acceptor) 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LReplicaNextProcessStartingPhase2(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_StartingPhase2? 
	&& 
	LExecutorProcessStartingPhase2(s.executor, s_next.executor, received_packet, sent_packets) 
	&& 
	s_next == s.(executor := s_next.executor)
}


predicate LReplicaNextProcess2a(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_2a? 
	&& 
	var m := 
		received_packet.msg; 	
	if received_packet.src in s.acceptor.constants.all.config.replica_ids && BalLeq(s.acceptor.max_bal, m.bal_2a) && LeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val) then 
		LAcceptorProcess2a(s.acceptor, s_next.acceptor, received_packet, sent_packets) 
		&& 
		s_next == s.(acceptor := s_next.acceptor) 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LReplicaNextProcess2b(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_2b? 
	&& 
	var opn := 
		received_packet.msg.opn_2b; 	
	if op_learnable then 
		LLearnerProcess2b(s.learner, s_next.learner, received_packet) 
		&& 
		sent_packets == [] 
		&& 
		s_next == s.(learner := s_next.learner) 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LReplicaNextProcessReply(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_Reply? 
	&& 
	sent_packets == [] 
	&& 
	s_next == s
}


predicate LReplicaNextProcessAppStateSupply(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_AppStateSupply? 
	&& 
	var opn_state_supply := 
		received_packet.msg.opn_state_supply; 	
	if src_valid && op_valid then 
		LLearnerForgetOperationsBefore(s.learner, s_next.learner, opn_state_supply) 
		&& 
		LExecutorProcessAppStateSupply(s.executor, s_next.executor, received_packet) 
		&& 
		sent_packets == [] 
		&& 
		s_next == s.(learner := s_next.learner, executor := s_next.executor) 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LReplicaNextProcessAppStateRequest(s: STUB, s_next: STUB, received_packet: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_AppStateRequest? 
	&& 
	LExecutorProcessAppStateRequest(s.executor, s_next.executor, received_packet, sent_packets) 
	&& 
	s_next == s.(executor := s_next.executor)
}


predicate LReplicaNextProcessHeartbeat(s: STUB, s_next: STUB, received_packet: STUB, clock: STUB, sent_packets: STUB) 
{
	received_packet.msg.type.RslMessage_Heartbeat? 
	&& 
	LProposerProcessHeartbeat(s.proposer, s_next.proposer, received_packet, clock) 
	&& 
	LAcceptorProcessHeartbeat(s.acceptor, s_next.acceptor, received_packet) 
	&& 
	sent_packets == [] 
	&& 
	s_next == s.(proposer := s_next.proposer, acceptor := s_next.acceptor)
}


predicate LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s: STUB, s_next: STUB, sent_packets: STUB) 
{
	LProposerMaybeEnterNewViewAndSend1a(s.proposer, s_next.proposer, sent_packets) 
	&& 
	s_next == s.(proposer := s_next.proposer)
}


predicate LReplicaNextSpontaneousMaybeEnterPhase2(s: STUB, s_next: STUB, sent_packets: STUB) 
{
	LProposerMaybeEnterPhase2(s.proposer, s_next.proposer, s.acceptor.log_truncation_point, sent_packets) 
	&& 
	s_next == s.(proposer := s_next.proposer)
}


predicate LReplicaNextReadClockMaybeNominateValueAndSend2a(s: STUB, s_next: STUB, clock: STUB, sent_packets: STUB) 
{
	LProposerMaybeNominateValueAndSend2a(s.proposer, s_next.proposer, clock.t, s.acceptor.log_truncation_point, sent_packets) 
	&& 
	s_next == s.(proposer := s_next.proposer)
}


predicate LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s: STUB, s_next: STUB, sent_packets: STUB) 
{
	(exists opn :: opn in s.acceptor.last_checkpointed_operation && IsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) && if opn > s.acceptor.log_truncation_point then LAcceptorTruncateLog(s.acceptor, s_next.acceptor, opn) && s_next == s.(acceptor := s_next.acceptor) && sent_packets == [] else s_next == s && sent_packets == [])
}


predicate LReplicaNextSpontaneousMaybeMakeDecision(s: STUB, s_next: STUB, sent_packets: STUB) 
{
	var opn := 
		s.executor.ops_complete; 	
	if s.executor.next_op_to_execute.type.OutstandingOpUnknown? && opn in s.learner.unexecuted_learner_state && |s.learner.unexecuted_learner_state[opn].received_2b_message_senders| >= LMinQuorumSize(s.learner.constants.all.config) then 
		LExecutorGetDecision(s.executor, s_next.executor, s.learner.max_ballot_seen, opn, s.learner.unexecuted_learner_state[opn].candidate_learned_value) 
		&& 
		s_next == s.(executor := s_next.executor) 
		&& 
		sent_packets == [] 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LReplicaNextSpontaneousMaybeExecute(s: STUB, s_next: STUB, sent_packets: STUB) 
{
	if s.executor.next_op_to_execute.type.OutstandingOpKnown? && s.executor.ops_complete < s.executor.constants.all.params.max_integer_val && LReplicaConstantsValid(s.executor.constants) then 
		var v := 
			s.executor.next_op_to_execute.v; 		
		LProposerResetViewTimerDueToExecution(s.proposer, s_next.proposer, v) 
		&& 
		LLearnerForgetDecision(s.learner, s_next.learner, s.executor.ops_complete) 
		&& 
		LExecutorExecute(s.executor, s_next.executor, sent_packets) 
		&& 
		s_next == s.(proposer := s_next.proposer, learner := s_next.learner, executor := s_next.executor) 
	else 
		s_next == s 
		&& 
		sent_packets == []
}


predicate LReplicaNextReadClockMaybeSendHeartbeat(s: STUB, s_next: STUB, clock: STUB, sent_packets: STUB) 
{
	if clock.t < s.nextHeartbeatTime then 
		s_next == s 
		&& 
		sent_packets == [] 
	else 
		var new_next_heartbeat := 
			UpperBoundedAddition(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val); 		
		s_next == s.(nextHeartbeatTime := new_next_heartbeat) 
		&& 
		sent_packets == LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, STUB("RslMessage_Heartbeat", s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete), sent_packets)
}


predicate LReplicaNextReadClockCheckForViewTimeout(s: STUB, s_next: STUB, clock: STUB, sent_packets: STUB) 
{
	LProposerCheckForViewTimeout(s.proposer, s_next.proposer, clock.t) 
	&& 
	sent_packets == [] 
	&& 
	s_next == s.(proposer := s_next.proposer)
}


predicate LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s: STUB, s_next: STUB, clock: STUB, sent_packets: STUB) 
{
	LProposerCheckForQuorumOfViewSuspicions(s.proposer, s_next.proposer, clock.t) 
	&& 
	sent_packets == [] 
	&& 
	s_next == s.(proposer := s_next.proposer)
}
