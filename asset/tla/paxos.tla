---- MODULE paxos ----

\******  types ********\

OperationNumber == Int

Ballot == [seqno: Int, proposer_id: Int]

Request == [client: NodeIdentity, seqno: Int, request:AppMessage]

Reply == [client:NodeIdentity, seqno:Int, reply:AppMessage]

RequestBatch == Seq(Request)

ReplyCache == [NodeIdentity -> Reply]

Vote == [max_value_bal:Ballot, max_val:RequestBatch]

Votes == [OperationNumber -> Vote]

LearnerTuple == [received_2b_message_senders: SUBSET NodeIdentity, candidate_learned_value:RequestBatch]

LearnerState == [OperationNumber -> LearnerTuple]

BalLt(ba, bb) ==
  \/ ba.seqno < bb.seqno
  \/ (ba.seqno = bb.seqno /\ ba.proposer_id < bb.proposer_id)

BalLeq(ba, bb) ==
  \/ ba.seqno < bb.seqno
  \/ (ba.seqno = bb.seqno /\ ba.proposer_id <= bb.proposer_id)

\******  configuration ********\

LConfiguration == [replica_ids: Seq(NodeIdentity)]

LMinQuorumSize(c) == Len(c.replica_ids) \div 2 + 1

ReplicasDistinct(replica_ids, i, j) ==
    /\ 0 <= i /\ i < Len(replica_ids)
    /\ (replica_ids[i] = replica_ids[j]) => (i = j)

ReplicasIsUnique(replica_ids) == 
     \A i, j : 
        (0 <= i /\ i < Len(replica_ids) /\ 0 <= j /\ j < Len(replica_ids))
        /\ (replica_ids[i] = replica_ids[j]) => (i = j)

WellFormedLConfiguration(c) ==
    /\ Len(c.replica_ids) > 0
    /\ \A i, j : ReplicasDistinct(c.replica_ids, i, j)
    /\ ReplicasIsUnique(c.replica_ids)

IsReplicaIndex(idx, id, c) == 
    /\ 0 <= idx 
    /\ idx < Len(c.replica_ids)
    /\ c.replica_ids[idx] = id

GetReplicaIndex(id, c) == 
    FindIndexInSeq(c.replica_ids, id)

\******  parameters ********\

LParameters == [
    max_log_length:Int,
    baseline_view_timeout_period:Int,
    heartbeat_period:Int,
    max_integer_val:UpperBound,
    max_batch_size:Int,
    max_batch_delay:Int
]

WFLParameters(p) ==
    /\ p.max_log_length > 0
    /\ p.baseline_view_timeout_period > 0
    /\ p.heartbeat_period > 0
    /\ (p.max_integer_val.UpperBoundFinite => p.max_integer_val.n > p.max_log_length)
    /\ p.max_batch_size > 0
    /\ p.max_batch_delay >= 0

\******  constants ********\

LConstants == [config: LConfiguration, params: LParameters]

LReplicaConstants == [my_index: Int, all: LConstants]

LReplicaConstantsValid(c) == 
    /\ 0 <= c.my_index 
    /\ c.my_index < Len(c.all.config.replica_ids)

\******  message ********\

\* RslMessage ==
\*     [type: {"RslMessage_Invalid"}] \cup
\*     [type: {"RslMessage_Request"}, seqno_req: Int, val: AppMessage] \cup
\*     [type: {"RslMessage_1a"}, bal_1a: Ballot] \cup
\*     [type: {"RslMessage_1b"}, bal_1b: Ballot, log_truncation_point: OperationNumber, votes: Votes] \cup
\*     [type: {"RslMessage_2a"}, bal_2a: Ballot, opn_2a: OperationNumber, val_2a: RequestBatch] \cup
\*     [type: {"RslMessage_2b"}, bal_2b: Ballot, opn_2b: OperationNumber, val_2b: RequestBatch] \cup
\*     [type: {"RslMessage_Heartbeat"}, bal_heartbeat: Ballot, suspicious: BOOLEAN, opn_ckpt: OperationNumber] \cup
\*     [type: {"RslMessage_Reply"}, seqno_reply: Int, reply: AppMessage] \cup
\*     [type: {"RslMessage_AppStateRequest"}, bal_state_req: Ballot, opn_state_req: OperationNumber] \cup
\*     [type: {"RslMessage_AppStateSupply"}, bal_state_supply: Ballot, opn_state_supply: OperationNumber, app_state: AppState, reply_cache: ReplyCache] \cup
\*     [type: {"RslMessage_StartingPhase2"}, bal_2: Ballot, logTruncationPoint_2: OperationNumber]

\******  environment ********\

RslEnvironment == LEnvironment(NodeIdentity, RslMessage)

RslPacket == LPacket(NodeIdentity, RslMessage)

RslIo == LIoOp(NodeIdentity, RslMessage)

\******  broadcast ********\

LBroadcastToEveryone(c, myidx, m, sent_packets) ==
    /\ Len(sent_packets) = Len(c.replica_ids)
    /\ 0 <= myidx 
    /\ myidx <= Len(c.replica_ids)
    /\ \A idx : 0 <= idx /\ idx < Len(sent_packets) 
        => sent_packets[idx] = [dst |-> c.replica_ids[idx], src |-> c.replica_ids[myidx + 1], msg |-> m] \* how to know the type of this initialization? *\

\******  clockreading ********\

ClockReading == [t:Int]

\******  acceptor ********\

LAcceptor == [
    constants: LReplicaConstants,
    max_bal: Ballot,
    votes: Votes,
    last_checkpointed_operation: Seq(OperationNumber),
    log_truncation_point: OperationNumber
]

IsLogTruncationPointValid(log_truncation_point, last_checkpointed_operation, config) ==
    IsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, LMinQuorumSize(config))

RemoveVotesBeforeLogTruncationPoint(votes, votes_next, log_truncation_point) ==
    /\ (\A opn : opn \in DOMAIN votes_next => opn \in DOMAIN votes /\ votes_next[opn] = votes[opn])
    /\ (\A opn : opn < log_truncation_point => opn \notin DOMAIN votes_next)
    /\ (\A opn : opn >= log_truncation_point => opn \in DOMAIN votes_next)
    /\ (\A opn : opn \in DOMAIN votes /\ opn >= log_truncation_point =>
         (opn \in DOMAIN votes_next /\ votes_next[opn] = votes[opn]))

LAddVoteAndRemoveOldOnes(votes, votes_next, new_opn, new_vote, log_truncation_point) ==
    /\ (\A opn :  opn \in DOMAIN votes_next => (opn >= log_truncation_point) /\ (opn \in DOMAIN votes \/ opn = new_opn))
    /\ (\A opn : (opn >= log_truncation_point) /\ (opn \in DOMAIN votes \/ opn = new_opn) => opn \in DOMAIN votes')
    /\ (\A opn : opn \in DOMAIN votes_next =>
         votes_next[opn] = IF opn = new_opn THEN new_vote ELSE votes[opn])

LAcceptorInit(a, c) ==
    /\ a.constants = c
    /\ a.max_bal = [ seqno |-> 0, proposer_id |-> 0 ]
    /\ a.votes = [ x \in {} |-> Vote ]
    /\ Len(a.last_checkpointed_operation) = Len(c.all.config.replica_ids)
    /\ (\A idx : 0 <= idx /\ idx < Len(a.last_checkpointed_operation) => a.last_checkpointed_operation[idx] = 0)
    /\ a.log_truncation_point = 0

LAcceptorProcess1a(s, s_next, inp, sent_packets) ==
    /\ inp.msg.type = "RslMessage_1a"
    /\ LET m == inp.msg IN
        /\ IF inp.src \in s.constants.all.config.replica_ids 
            /\ BalLt(s.max_bal, m.bal_1a)
            /\ LReplicaConstantsValid(s.constants)
            THEN
                /\ sent_packets = << [ dst |-> inp.src,
                                        src |-> s.constants.all.config.replica_ids[s.constants.my_index],
                                        msg |-> [ type |-> "RslMessage_1b",
                                                    bal_1b |-> m.bal_1a,
                                                    log_truncation_point |-> s.log_truncation_point,
                                                    votes |-> s.votes ] ] >>
                /\ s_next = [ s EXCEPT !.max_bal = m.bal_1a ]
            ELSE
                /\ sent_packets = <<>>
                /\ s_next = s

LAcceptorProcess2a(s, s_next, inp, sent_packets) ==
    /\ inp.msg.type = "RslMessage_2a"  
    /\ inp.src \in s.constants.all.config.replica_ids
    /\ BalLeq(s.max_bal, inp.msg.bal_2a)
    /\ LeqUpperBound(inp.msg.opn_2a, s.constants.all.params.max_integer_val)
    /\ LET m == inp.msg IN
        LET newLogTruncationPoint ==
            IF (m.opn_2a - s.constants.all.params.max_log_length + 1 > s.log_truncation_point)
            THEN m.opn_2a - s.constants.all.params.max_log_length + 1
            ELSE s.log_truncation_point
        IN
            /\ LBroadcastToEveryone(s.constants.all.config,
                                    s.constants.my_index,
                                    [ type |-> "RslMessage_2b",
                                    bal_2b |-> m.bal_2a,
                                    opn_2b |-> m.opn_2a,
                                    val_2b |-> m.val_2a ],
                                    sent_packets)
            /\ s_next = [ s EXCEPT
                            !.max_bal = m.bal_2a,
                            !.log_truncation_point = newLogTruncationPoint,
                            !.votes = IF s.log_truncation_point <= m.opn_2a
                                    THEN LAddVoteAndRemoveOldOnes(s.votes,
                                                                    s_next.votes,
                                                                    m.opn_2a,
                                                                    [ max_value_bal |-> m.bal_2a, max_val |-> m.val_2a ],
                                                                    newLogTruncationPoint)
                                    ELSE s.votes
                    ]

LAcceptorProcessHeartbeat(s, s_next, inp) ==
    /\ inp.msg.type = "RslMessage_Heartbeat"
    /\ IF inp.src \in s.constants.all.config.replica_ids
       THEN
          LET sender_index == GetReplicaIndex(inp.src, s.constants.all.config) IN
              IF 0 <= sender_index
                 /\ sender_index <= Len(s.last_checkpointed_operation)
                 /\ inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index]
              THEN
                 /\ s_next = [ s EXCEPT !.last_checkpointed_operation[sender_index] = inp.msg.opn_ckpt ]
              ELSE
                 /\ s_next = s
       ELSE
          /\ s_next = s

LAcceptorTruncateLog(s, s_next, opn) ==
    IF opn <= s.log_truncation_point
    THEN s_next = s
    ELSE
        /\ RemoveVotesBeforeLogTruncationPoint(s.votes, s_next.votes, opn)
        /\ s_next = [ s EXCEPT !.log_truncation_point = opn, !.votes = s_next.votes]

\******  learner ********\

LLearner == [
    constants: LReplicaConstants,
    max_ballot_seen: Ballot,
    unexecuted_learner_state: LearnerState
]

LLearnerInit(l, c) ==
    /\ l.constants = c
    /\ l.max_ballot_seen = [ seqno |-> 0, proposer_id |-> 0 ]
    /\ l.unexecuted_learner_state = [ x \in {} |-> LearnerTuple ]

LLearnerProcess2b(s, s_next, packet) ==
    /\ packet.msg.type = "RslMessage_2b"
    /\ LET m == packet.msg IN
       LET opn == m.opn_2b IN
           IF packet.src \notin s.constants.all.config.replica_ids
              \/ BalLt(m.bal_2b, s.max_ballot_seen)
           THEN
               /\ s_next = s
           ELSE IF BalLt(s.max_ballot_seen, m.bal_2b)
           THEN
               LET tup_next == [ received_2b_message_senders |-> {packet.src}, 
                             candidate_learned_value |-> m.val_2b ] IN
               /\ s_next = [ s EXCEPT !.max_ballot_seen = m.bal_2b,
                                    !.unexecuted_learner_state[opn] = tup_next ]
           ELSE IF opn \notin DOMAIN s.unexecuted_learner_state
           THEN
               LET tup_next == [ received_2b_message_senders |-> {packet.src}, 
                             candidate_learned_value |-> m.val_2b ] IN
               /\ s_next = [ s EXCEPT !.unexecuted_learner_state[opn] = tup_next ]
           ELSE IF packet.src \in s.unexecuted_learner_state[opn].received_2b_message_senders
           THEN
               /\ s_next = s
           ELSE
                LET tup == s.unexecuted_learner_state[opn] IN
                LET tup_next == [ tup EXCEPT !.received_2b_message_senders = tup.received_2b_message_senders \cup {packet.src} ] IN
                /\ s_next = [ s EXCEPT !.unexecuted_learner_state[opn] = tup_next ]

LLearnerForgetDecision(s, s_next, opn) ==
    IF opn \in DOMAIN s.unexecuted_learner_state
    THEN
        /\ s_next = [ s EXCEPT !.unexecuted_learner_state = RemoveElt(s.unexecuted_learner_state, opn) ]
    ELSE
        /\ s_next = s

\* LLearnerForgetOperationsBefore(s, s_next, ops_complete) ==
\*     LET new_learner_state == [op \in {op_ \in DOMAIN s.unexecuted_learner_state : op_ >= ops_complete} |-> s.unexecuted_learner_state[op]] IN
\*     /\ s_next = [ s EXCEPT !.unexecuted_learner_state = new_learner_state]

\******  election ********\

ElectionState == [
    constants: LReplicaConstants,
    current_view: Ballot,
    current_view_suspectors: SUBSET Int, \* this is set<int> *\
    epoch_end_time: Int,
    epoch_length: Int,
    requests_received_this_epoch: Seq(Request),
    requests_received_prev_epochs: Seq(Request)
]

ComputeSuccessorView(b, c) ==
    IF b.proposer_id + 1 < Len(c.config.replica_ids)
    THEN [ seqno |-> b.seqno, proposer_id |-> b.proposer_id + 1 ]
    ELSE [ seqno |-> b.seqno + 1, proposer_id |-> 0 ]

BoundRequestSequence(s, lengthBound) ==
    IF lengthBound.type = "UpperBoundFinite" 
       /\ 0 <= lengthBound.n
       /\ lengthBound.n < Len(s)
    THEN SubSeq(s, 0, lengthBound.n) 
    ELSE s

RequestsMatch(r1, r2) ==
    /\ r1.type = "Request"
    /\ r2.type = "Request"
    /\ r1.client = r2.client
    /\ r1.seqno = r2.seqno

RequestSatisfiedBy(r1, r2) ==
    /\ r1.type = "Request"
    /\ r2.type = "Request"
    /\ r1.client = r2.client
    /\ r1.seqno <= r2.seqno

\* RECURSIVE RemoveAllSatisfiedRequestsInSequence(_, _)

RemoveAllSatisfiedRequestsInSequence(s, r) ==
    IF Len(s) = 0 
    THEN <<>> 
    ELSE IF RequestSatisfiedBy(s[0], r)
    THEN RemoveAllSatisfiedRequestsInSequence(SubSeq(s, 1, Len(s)), r)
    ELSE << s[0] >> \o RemoveAllSatisfiedRequestsInSequence(SubSeq(s, 1, Len(s)), r)

ElectionStateInit(es, c) ==
    /\ Len(c.all.config.replica_ids) > 0
    /\ es.constants = c
    /\ es.current_view = [ seqno |-> 1, proposer_id |-> 0 ]
    /\ es.current_view_suspectors = {}
    /\ es.epoch_end_time = 0
    /\ es.epoch_length = c.all.params.baseline_view_timeout_period
    /\ es.requests_received_this_epoch = <<>>
    /\ es.requests_received_prev_epochs = <<>>

ElectionStateProcessHeartbeat(es, es_next, p, clock) ==
    /\ p.msg.type = "RslMessage_Heartbeat"
    /\ IF p.src \notin es.constants.all.config.replica_ids
       THEN
           /\ es_next = es
       ELSE
           LET sender_index == GetReplicaIndex(p.src, es.constants.all.config) IN
               IF p.msg.bal_heartbeat = es.current_view /\ p.msg.suspicious
               THEN
                   /\ es_next = [ es EXCEPT !.current_view_suspectors = es.current_view_suspectors \cup {sender_index} ]
               ELSE IF BalLt(es.current_view, p.msg.bal_heartbeat)
               THEN
                   LET new_epoch_length == UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val) IN
                   /\ es_next = [ es EXCEPT !.current_view = p.msg.bal_heartbeat,
                                          !.current_view_suspectors = IF p.msg.suspicious THEN {sender_index} ELSE {},
                                          !.epoch_length = new_epoch_length,
                                          !.epoch_end_time = UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val),
                                          !.requests_received_prev_epochs = BoundRequestSequence(es.requests_received_prev_epochs \o es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
                                          !.requests_received_this_epoch = <<>> ]
               ELSE
                   /\ es_next = es

ElectionStateCheckForViewTimeout(es, es_next, clock) ==
    IF clock < es.epoch_end_time
    THEN
        /\ es_next = es
    ELSE IF Len(es.requests_received_prev_epochs) = 0
    THEN
        LET new_epoch_length == es.constants.all.params.baseline_view_timeout_period IN
        /\ es_next = [ es EXCEPT !.epoch_length = new_epoch_length,
                                  !.epoch_end_time = UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val),
                                  !.requests_received_prev_epochs = es.requests_received_this_epoch,
                                  !.requests_received_this_epoch = <<>> ]
    ELSE
        /\ es_next = [ es EXCEPT !.current_view_suspectors = es.current_view_suspectors \cup {es.constants.my_index},
                                  !.epoch_end_time = UpperBoundedAddition(clock, es.epoch_length, es.constants.all.params.max_integer_val),
                                  !.requests_received_prev_epochs = BoundRequestSequence(es.requests_received_prev_epochs \o es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
                                  !.requests_received_this_epoch = <<>> ]

ElectionStateCheckForQuorumOfViewSuspicions(es, es_next, clock) ==
    IF Cardinality(es.current_view_suspectors) < LMinQuorumSize(es.constants.all.config)
       \/ ~LtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val)
    THEN
        /\ es_next = es
    ELSE
        LET new_epoch_length == UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val) IN
        /\ es_next = [ es EXCEPT !.current_view = ComputeSuccessorView(es.current_view, es.constants.all),
                                  !.current_view_suspectors = {},
                                  !.epoch_length = new_epoch_length,
                                  !.epoch_end_time = UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val),
                                  !.requests_received_prev_epochs = BoundRequestSequence(es.requests_received_prev_epochs \o es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
                                  !.requests_received_this_epoch = <<>> ]

ElectionStateReflectReceivedRequest(es, es_next, req) ==
    IF \E earlier_req : (earlier_req \in es.requests_received_prev_epochs \/ earlier_req \in es.requests_received_this_epoch)
        /\ RequestsMatch(earlier_req, req)
    THEN
        /\ es_next = es
    ELSE
        /\ es_next = [ es EXCEPT !.requests_received_this_epoch = BoundRequestSequence(es.requests_received_this_epoch \o <<req>>, es.constants.all.params.max_integer_val) ]

\* RECURSIVE RemoveExecutedRequestBatch(_, _)

RemoveExecutedRequestBatch(reqs, batch) ==
    IF Len(batch) = 0 
    THEN reqs
    ELSE RemoveExecutedRequestBatch(RemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), SubSeq(batch, 1, Len(batch)))

ElectionStateReflectExecutedRequestBatch(es, es_next, batch) ==
    /\ es_next = [ es EXCEPT 
                    !.requests_received_prev_epochs = RemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch),
                    !.requests_received_this_epoch = RemoveExecutedRequestBatch(es.requests_received_this_epoch, batch) ]

\******  proposer ********\

\* IncompleteBatchTimer == 
\*     [type:{"IncompleteBatchTimerOn"}, when:Int] \cup 
\*     [type:{"IncompleteBatchTimerOff"}]

LProposer == [
    constants: LReplicaConstants,
    current_state: Int,
    request_queue: Seq(Request),
    max_ballot_i_sent_1a: Ballot,
    next_operation_number_to_propose: Int,
    received_1b_packets: SUBSET RslPacket, \* set<RslPacket> *\
    highest_seqno_requested_by_client_this_view: [NodeIdentity -> Int], \* map<NodeIdentity, int> *\
    incomplete_batch_timer: IncompleteBatchTimer,
    election_state: ElectionState
]

LIsAfterLogTruncationPoint(opn, received_1b_packets) ==
    \A p : p \in received_1b_packets /\
        p.msg.type = "RslMessage_1b" => p.msg.log_truncation_point <= opn

LSetOfMessage1b(S) ==
    \A p : p \in S => p.msg.type = "RslMessage_1b"

LSetOfMessage1bAboutBallot(S, b) ==
    /\ LSetOfMessage1b(S)
    /\ \A p : p \in S => p.msg.bal_1b = b

LExistVotesHasProposalLargeThanOpn(p, op) ==
    /\ p.msg.type = "RslMessage_1b"
    /\ \E opn : opn \in DOMAIN p.msg.votes /\ opn > op

LExistsAcceptorHasProposalLargeThanOpn(S, op) ==
    /\ LSetOfMessage1b(S)
    /\ \E p : p \in S /\ LExistVotesHasProposalLargeThanOpn(p, op)

LAllAcceptorsHadNoProposal(S, opn) ==
    /\ LSetOfMessage1b(S)
    /\ \A p : p \in S => opn \notin DOMAIN p.msg.votes

Lmax_balInS(c, S, opn) ==
    /\ LSetOfMessage1b(S)
    /\ \A p : p \in S /\ opn \in DOMAIN p.msg.votes => BalLeq(p.msg.votes[opn].max_value_bal, c)

LExistsBallotInS(v, c, S, opn) ==
    /\ LSetOfMessage1b(S)
    /\ \E p : p \in S /\ opn \in DOMAIN p.msg.votes 
                     /\ p.msg.votes[opn].max_value_bal = c
                     /\ p.msg.votes[opn].max_val = v

LValIsHighestNumberedProposalAtBallot(v, c, S, opn) ==
    /\ Lmax_balInS(c, S, opn)
    /\ LExistsBallotInS(v, c, S, opn)

LValIsHighestNumberedProposal(v, S, opn) ==
    /\ LSetOfMessage1b(S)
    /\ \E c : LValIsHighestNumberedProposalAtBallot(v, c, S, opn)

LProposerCanNominateUsingOperationNumber(s, log_truncation_point, opn) ==
    /\ s.election_state.current_view = s.max_ballot_i_sent_1a
    /\ s.current_state = 2
    /\ Cardinality(s.received_1b_packets) >= LMinQuorumSize(s.constants.all.config)
    /\ LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
    /\ LIsAfterLogTruncationPoint(opn, s.received_1b_packets)
    /\ opn < UpperBoundedAddition(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val)
    /\ opn >= 0
    /\ LtUpperBound(opn, s.constants.all.params.max_integer_val)

LProposerInit(s, c) ==
    /\ WellFormedLConfiguration(c.all.config)
    /\ s.constants = c
    /\ s.current_state = 0
    /\ s.request_queue = <<>> 
    /\ s.max_ballot_i_sent_1a = [ seqno |-> 0, proposer_id |-> c.my_index ]
    /\ s.next_operation_number_to_propose = 0
    /\ s.received_1b_packets = {}
    /\ s.highest_seqno_requested_by_client_this_view = [ x \in {} |-> Int ]
    /\ ElectionStateInit(s.election_state, c)
    /\ s.incomplete_batch_timer.type = "IncompleteBatchTimerOff" 

LProposerProcessRequest(s, s_next, packet) ==
    /\ packet.msg.type = "RslMessage_Request"
    /\ LET val == [ client |-> packet.src,
                    seqno |-> packet.msg.seqno_req,
                    request |-> packet.msg.val ] 
       IN
        /\ ElectionStateReflectReceivedRequest(s.election_state, s_next.election_state, val)
        /\ IF s.current_state # 0
             /\ (val.client \notin DOMAIN s.highest_seqno_requested_by_client_this_view
                 \/ val.seqno > s.highest_seqno_requested_by_client_this_view[val.client])
           THEN
              /\ s_next = [ s EXCEPT 
                             !.election_state = s_next.election_state,
                             !.request_queue = s.request_queue \o <<val>>,
                             !.highest_seqno_requested_by_client_this_view[val.client] = val.seqno ]
           ELSE
              /\ s_next = [ s EXCEPT 
                             !.election_state = s_next.election_state ]

LProposerMaybeEnterNewViewAndSend1a(s, s_next, sent_packets) ==
    IF s.election_state.current_view.proposer_id = s.constants.my_index
       /\ BalLt(s.max_ballot_i_sent_1a, s.election_state.current_view)
    THEN
        /\ s_next = [ s EXCEPT 
                       !.current_state = 1,
                       !.max_ballot_i_sent_1a = s.election_state.current_view,
                       !.received_1b_packets = {},
                       !.highest_seqno_requested_by_client_this_view = [ x \in {} |-> Int ],
                       !.request_queue = s.election_state.requests_received_prev_epochs \o s.election_state.requests_received_this_epoch ]
        /\ LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, 
                                [ type |-> "RslMessage_1a", bal_1a |-> s.election_state.current_view ], 
                                sent_packets)
    ELSE
        /\ s_next = s
        /\ sent_packets = <<>>

LProposerProcess1b(s, s_next, p) ==
    /\ p.msg.type = "RslMessage_1b"
    /\ p.src \in s.constants.all.config.replica_ids
    /\ p.msg.bal_1b = s.max_ballot_i_sent_1a
    /\ s.current_state = 1
    /\ (\A other_packet : other_packet \in s.received_1b_packets => (other_packet.src # p.src))
    /\ s_next = [ s EXCEPT !.received_1b_packets = s.received_1b_packets \union { p } ]

LProposerMaybeEnterPhase2(s, s_next, log_truncation_point, sent_packets) ==
    IF Cardinality(s.received_1b_packets) >= LMinQuorumSize(s.constants.all.config)
       /\ LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
       /\ s.current_state = 1
    THEN
        /\ s_next = [ s EXCEPT 
                       !.current_state = 2,
                       !.next_operation_number_to_propose = log_truncation_point ]
        /\ LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, 
                                [ type |-> "RslMessage_StartingPhase2",
                                  bal_2 |-> s.max_ballot_i_sent_1a,
                                  logTruncationPoint_2 |-> log_truncation_point ], 
                                sent_packets)
    ELSE
        /\ s_next = s
        /\ sent_packets = <<>>

LProposerNominateNewValueAndSend2a(s, s_next, clock, log_truncation_point, sent_packets) ==
    /\ LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
    /\ LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    /\ LET batchSize == IF Len(s.request_queue) <= s.constants.all.params.max_batch_size 
                           \/ s.constants.all.params.max_batch_size < 0
                        THEN Len(s.request_queue)
                        ELSE s.constants.all.params.max_batch_size
       IN
        /\ LET v == SubSeq(s.request_queue, 0, batchSize)
           IN
            /\ LET opn == s.next_operation_number_to_propose
               IN
                /\ s_next = [ s EXCEPT 
                               !.request_queue = SubSeq(s.request_queue, batchSize, Len(s.request_queue)),
                               !.next_operation_number_to_propose = s.next_operation_number_to_propose + 1,
                               !.incomplete_batch_timer = 
                                    IF Len(s.request_queue) > batchSize
                                    THEN [ type |-> "IncompleteBatchTimerOn",
                                           timeout |-> UpperBoundedAddition(clock, 
                                                                            s.constants.all.params.max_batch_delay,
                                                                            s.constants.all.params.max_integer_val) ]
                                    ELSE [ type |-> "IncompleteBatchTimerOff" ] ]
                /\ LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, 
                                        [ type |-> "RslMessage_2a", 
                                          bal_2a |-> s.max_ballot_i_sent_1a, 
                                          opn_2a |-> opn, 
                                          val_2a |-> v ], 
                                        sent_packets)

LProposerNominateOldValueAndSend2a(s, s_next, log_truncation_point, sent_packets) ==
    /\ LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
    /\ ~LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    /\ LET opn == s.next_operation_number_to_propose
       IN
        \E p : 
            /\ p \in s.received_1b_packets 
            /\ opn \in DOMAIN p.msg.votes
            /\ LValIsHighestNumberedProposal(p.msg.votes[opn].max_val, s.received_1b_packets, opn)
            /\ s_next = [ s EXCEPT 
                           !.next_operation_number_to_propose = s.next_operation_number_to_propose + 1 ]
            /\ LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, 
                                    [ type |-> "RslMessage_2a", 
                                      bal_2a |-> s.max_ballot_i_sent_1a, 
                                      opn_2a |-> opn, 
                                      val_2a |-> p.msg.votes[opn].max_val ], 
                                    sent_packets)

LProposerMaybeNominateValueAndSend2a(s, s_next, clock, log_truncation_point, sent_packets) ==
    IF ~LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
    THEN
        /\ s_next = s
        /\ sent_packets = <<>>
    ELSE IF ~LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    THEN
        /\ LProposerNominateOldValueAndSend2a(s, s_next, log_truncation_point, sent_packets)
    ELSE IF LExistsAcceptorHasProposalLargeThanOpn(s.received_1b_packets, s.next_operation_number_to_propose)
            \/ Len(s.request_queue) >= s.constants.all.params.max_batch_size
            \/ (Len(s.request_queue) > 0 
                /\ s.incomplete_batch_timer.type = "IncompleteBatchTimerOn"
                /\ clock >= s.incomplete_batch_timer.when)
    THEN
        /\ LProposerNominateNewValueAndSend2a(s, s_next, clock, log_truncation_point, sent_packets)
    ELSE IF Len(s.request_queue) > 0 
            /\ s.incomplete_batch_timer.type = "IncompleteBatchTimerOff"
    THEN
        /\ s_next = [ s EXCEPT 
                       !.incomplete_batch_timer = [ type |-> "IncompleteBatchTimerOn", 
                                                    when |-> UpperBoundedAddition(clock, 
                                                                                 s.constants.all.params.max_batch_delay, 
                                                                                 s.constants.all.params.max_integer_val) ] ]
        /\ sent_packets = <<>>
    ELSE
        /\ s_next = s
        /\ sent_packets = <<>>

LProposerProcessHeartbeat(s, s_next, p, clock) ==
    /\ p.msg.type = "RslMessage_Heartbeat"
    /\ ElectionStateProcessHeartbeat(s.election_state, s_next.election_state, p, clock)
    /\ IF BalLt(s.election_state.current_view, s_next.election_state.current_view)
       THEN 
            /\ s_next.current_state = 0
            /\ s_next.request_queue = <<>>
       ELSE 
            /\ s_next.current_state = s.current_state
            /\ s_next.request_queue = s.request_queue
            /\ s_next = [ s EXCEPT 
                   !.election_state = s_next.election_state,
                   !.current_state = s_next.current_state,
                   !.request_queue = s_next.request_queue ]

LProposerCheckForViewTimeout(s, s_next, clock) ==
    /\ ElectionStateCheckForViewTimeout(s.election_state, s_next.election_state, clock)
    /\ s_next = [ s EXCEPT !.election_state = s_next.election_state ]

LProposerCheckForQuorumOfViewSuspicions(s, s_next, clock) ==
    /\ ElectionStateCheckForQuorumOfViewSuspicions(s.election_state, s_next.election_state, clock)
    /\ IF BalLt(s.election_state.current_view, s_next.election_state.current_view)
       THEN 
            /\ s_next.current_state = 0
            /\ s_next.request_queue = <<>>
       ELSE 
            /\ s_next.current_state = s.current_state
            /\ s_next.request_queue = s.request_queue
            /\ s_next = [ s EXCEPT 
                   !.election_state = s_next.election_state,
                   !.current_state = s_next.current_state,
                   !.request_queue = s_next.request_queue ]

LProposerResetViewTimerDueToExecution(s, s_next, val) ==
    /\ ElectionStateReflectExecutedRequestBatch(s.election_state, s_next.election_state, val)
    /\ s_next = [ s EXCEPT !.election_state = s_next.election_state ]

\******  state machine ********\

HandleRequest(state, request) ==
    LET result == AppHandleRequest(state, request.request) IN
        << result[1], 
           [ client |-> request.client, 
             seqno  |-> request.seqno, 
             reply  |-> result[2] ] >>

\* RECURSIVE HandleRequestBatchHidden(_, _)

HandleRequestBatchHidden(state, batch) ==
    IF Len(batch) = 0 
    THEN << state >>
    ELSE 
        LET result1  == HandleRequestBatchHidden(state, SubSeq(batch, 0, Len(batch)-1))
            result2  == AppHandleRequest(result1[0][Len(result1[0])-1], batch[Len(batch)-1].request)
        IN << result1[1] \o << result2[1] >>, 
               result1[2] \o << [ client |-> batch[Len(batch)-1].client, 
                                   seqno  |-> batch[Len(batch)-1].seqno, 
                                   reply  |-> result2[2] ] >> >>

HandleRequestBatch(state, batch) ==
    HandleRequestBatchHidden(state, batch)

\******  executor ********\

\* OutstandingOperation == 
\*     [type:{"OutstandingOpKnown"}, v:RequestBatch, bal:Ballot] \cup 
\*     [type:{"OutstandingOpUnknown"}]

LExecutor == [constants: LReplicaConstants,
              app: AppState,
              ops_complete: Int,
              max_bal_reflected: Ballot,
              next_op_to_execute: OutstandingOperation,
              reply_cache: ReplyCache]

LExecutorInit(s, c) ==
    /\ s.constants = c
    /\ s.app = 0
    /\ s.ops_complete = 0
    /\ s.max_bal_reflected = [ seqno |-> 0, proposer_id |-> 0 ]
    /\ s.next_op_to_execute = [ type |-> "OutstandingOpKnown"]
    /\ s.reply_cache = [ x \in {} |-> Reply ]

LExecutorGetDecision(s, s_next, bal, opn, v) ==
    /\ opn = s.ops_complete
    /\ s.next_op_to_execute.type = "OutstandingOpUnknown"
    /\ s_next = [ s EXCEPT !.next_op_to_execute = [ type |-> "OutstandingOpKnown", v |-> v, bal |-> bal ] ]

\* RECURSIVE GetPacketsFromReplies(_, _, _)

GetPacketsFromReplies(me, requests, replies) ==
    IF Len(requests) = 0 
    THEN <<>> 
    ELSE 
        LET p == [ dst |-> requests[0].client,
                   src |-> me,
                   msg |-> [ type |-> "RslMessage_Reply",
                             seqno |-> requests[0].seqno,
                             reply |-> replies[0].reply ] ]
        IN << p >> \o GetPacketsFromReplies(me, SubSeq(requests, 1, Len(requests)), SubSeq(replies, 1, Len(replies)))

\* RECURSIVE LClientsInReplies(_)

\* LClientsInReplies(replies) ==
\*     IF Len(replies) = 0 
\*     THEN [ c \in {} |-> Reply ]
\*     ELSE [ LClientsInReplies(SubSeq(replies, 1, Len(replies))) EXCEPT ![replies[0].client] = replies[0] ] 

UpdateNewCache(c, c_next, replies) ==
    LET nc == LClientsInReplies(replies)
    IN 
    /\ \A client : client \in DOMAIN c_next =>  
          \/ (client \in DOMAIN c /\ c_next[client] = c[client])
          \/ (\E req_idx : 0 <= req_idx /\ req_idx < Len(replies) 
                /\ replies[req_idx].client = client
                /\ c_next[client] = replies[req_idx])
    /\ \A client : client \in DOMAIN c_next => client \in DOMAIN c \/ client \in DOMAIN nc
    /\ \A client : client \in DOMAIN c \/ client \in DOMAIN nc => client \in DOMAIN c_next
    /\ \A client : client \in DOMAIN c_next => c_next[client] = IF client \in DOMAIN c THEN c[client] ELSE nc[client]

LExecutorExecute(s, s_next, sent_packets) ==
    /\ s.next_op_to_execute.type = "OutstandingOpKnown"
    /\ LtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val)
    /\ LReplicaConstantsValid(s.constants)
    /\ LET batch == s.next_op_to_execute.value
            temp   == HandleRequestBatch(s.app, batch)
            new_state == temp[1][Len(temp[1])-1] 
            replies   == temp[2]
        IN
        /\ s_next.constants = s.constants 
        /\ s_next.app = new_state
        /\ s_next.ops_complete = s.ops_complete + 1
        /\ s_next.max_bal_reflected = IF BalLeq(s.max_bal_reflected, s.next_op_to_execute.ballot)
                                            THEN s.next_op_to_execute.ballot
                                            ELSE s.max_bal_reflected
        /\ s_next.next_op_to_execute = [ type |-> "OutstandingOpUnknown" ]
        /\ UpdateNewCache(s.reply_cache, s_next.reply_cache, replies)
        /\ sent_packets = GetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies)

LExecutorProcessAppStateSupply(s, s_next, inp) ==
    /\ inp.msg.type = "RslMessage_AppStateSupply"
    /\ inp.src \in s.constants.all.config.replica_ids
    /\ inp.msg.opn_state_supply > s.ops_complete
    /\ s_next = [ s EXCEPT
                    !.app = inp.msg.app_state,
                    !.ops_complete = inp.msg.opn_state_supply,
                    !.max_bal_reflected = inp.msg.bal_state_supply,
                    !.next_op_to_execute = [ type |-> "OutstandingOpUnknown" ],
                    !.reply_cache = inp.msg.reply_cache ]

LExecutorProcessAppStateRequest(s, s_next, inp, sent_packets) ==
    /\ inp.msg.type = "RslMessage_AppStateRequest"
    /\ LET m == inp.msg IN
        IF /\ inp.src \in s.constants.all.config.replica_ids
            /\ BalLeq(s.max_bal_reflected, m.bal_state_req)
            /\ s.ops_complete >= m.opn_state_req
            /\ LReplicaConstantsValid(s.constants)
        THEN
            /\ s_next = s
            /\ sent_packets = << [ dst |-> inp.src,
                                    src |-> s.constants.all.config.replica_ids[s.constants.my_index],
                                    msg |-> [ type |-> "RslMessage_AppStateSupply",
                                                bal_state_supply |-> s.max_bal_reflected,
                                                opn_state_supply |-> s.ops_complete,
                                                app_state |-> s.app,
                                                reply_cache |-> s.reply_cache ] ] >>
        ELSE
            /\ s_next = s
            /\ sent_packets = <<>>

LExecutorProcessStartingPhase2(s, s_next, inp, sent_packets) ==
    /\ inp.msg.type = "RslMessage_StartingPhase2"
    /\ LET m == inp.msg IN
        IF /\ inp.src \in s.constants.all.config.replica_ids
            /\ m.logTruncationPoint_2 > s.ops_complete
        THEN
            /\ s_next = s
            /\ LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                    [ type |-> "RslMessage_AppStateRequest",
                                        bal_state_req |-> m.bal_2,
                                        opn_state_req |-> m.logTruncationPoint_2 ], sent_packets)
        ELSE
            /\ s_next = s
            /\ sent_packets = <<>>

LExecutorProcessRequest(s, inp, sent_packets) ==
    /\ inp.msg.type = "RslMessage_Request"
    /\ inp.src \in DOMAIN s.reply_cache
    \* /\ s.reply_cache[inp.src].type = "Reply"
    /\ inp.msg.seqno_req <= s.reply_cache[inp.src].seqno
    /\ LET r == s.reply_cache[inp.src] IN
        IF /\ inp.msg.seqno_req = r.seqno
            /\ LReplicaConstantsValid(s.constants)
        THEN
            /\ sent_packets = << [ dst |-> r.client,
                                    src |-> s.constants.all.config.replica_ids[s.constants.my_index],
                                    msg |-> [ type |-> "RslMessage_Reply",
                                                seqno_reply |-> r.seqno,
                                                reply |-> r.reply ] ] >>
        ELSE
            /\ sent_packets = <<>>

\******  replica ********\

LReplica == [constants: LReplicaConstants,
             nextHeartbeatTime: Int,
             proposer: LProposer,
             acceptor: LAcceptor,
             learner: LLearner,
             executor: LExecutor]

LReplicaInit(r, c) ==
    /\ WellFormedLConfiguration(c.all.config)
    /\ r.constants = c 
    /\ r.nextHeartbeatTime = 0
    /\ LProposerInit(r.proposer, c)
    /\ LAcceptorInit(r.acceptor, c)
    /\ LLearnerInit(r.learner, c)
    /\ LExecutorInit(r.executor, c)

LReplicaNextProcessInvalid(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_Invalid"
    /\ s_next = s
    /\ sent_packets = <<>>

LReplicaNextProcessRequest(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_Request"
    /\ IF /\ received_packet.src \in DOMAIN s.executor.reply_cache
            \* /\ s.executor.reply_cache[received_packet.src].type = "Reply"
            /\ received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno
        THEN
            /\ LExecutorProcessRequest(s.executor, received_packet, sent_packets)
            /\ s_next = s
        ELSE
            /\ LProposerProcessRequest(s.proposer, s_next.proposer, received_packet)
            /\ sent_packets = <<>>
            /\ s_next = [ s EXCEPT !.proposer = s_next.proposer ]

LReplicaNextProcess1a(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_1a"
    /\ LAcceptorProcess1a(s.acceptor, s_next.acceptor, received_packet, sent_packets)
    /\ s_next = [ s EXCEPT !.acceptor = s_next.acceptor ]

LReplicaNextProcess1b(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_1b"
    /\ LET proposerConfig == s.proposer.constants.all.config.replica_ids
          proposerBallot == s.proposer.max_ballot_i_sent_1a
          proposerState == s.proposer.current_state
          proposerReceived == s.proposer.received_1b_packets
       IN
       IF /\ received_packet.src \in proposerConfig
          /\ received_packet.msg.bal_1b = proposerBallot
          /\ proposerState = 1
          /\ (\A other_packet : other_packet \in proposerReceived => other_packet.src # received_packet.src)
       THEN
          /\ LProposerProcess1b(s.proposer, s_next.proposer, received_packet)
          /\ LAcceptorTruncateLog(s.acceptor, s_next.acceptor, received_packet.msg.log_truncation_point)
          /\ sent_packets = <<>>
          /\ s_next = [ s EXCEPT !.proposer = s_next.proposer, !.acceptor = s_next.acceptor ]
       ELSE
          /\ s_next = s
          /\ sent_packets = <<>>

LReplicaNextProcessStartingPhase2(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_StartingPhase2"
    /\ LExecutorProcessStartingPhase2(s.executor, s_next.executor, received_packet, sent_packets)
    /\ s_next = [ s EXCEPT !.executor = s_next.executor ]

LReplicaNextProcess2a(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_2a"
    /\ LET m == received_packet.msg IN
       IF /\ received_packet.src \in s.acceptor.constants.all.config.replica_ids
          /\ BalLeq(s.acceptor.max_bal, m.bal_2a)
          /\ LeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val)
       THEN
          /\ LAcceptorProcess2a(s.acceptor, s_next.acceptor, received_packet, sent_packets)
          /\ s_next = [ s EXCEPT !.acceptor = s_next.acceptor ]
       ELSE
          /\ s_next = s
          /\ sent_packets = <<>>

LReplicaNextProcess2b(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_2b"
    /\ LET opn == received_packet.msg.opn_2b
          op_learnable == (s.executor.ops_complete < opn) 
                          \/ (s.executor.ops_complete = opn 
                                /\ s.executor.next_op_to_execute.type = "OutstandingOpUnknown")
       IN
       IF op_learnable
       THEN
          /\ LLearnerProcess2b(s.learner, s_next.learner, received_packet)
          /\ sent_packets = <<>>
          /\ s_next = [ s EXCEPT !.learner = s_next.learner ]
       ELSE
          /\ s_next = s
          /\ sent_packets = <<>>


LReplicaNextProcessReply(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_Reply"
    /\ sent_packets = <<>>
    /\ s_next = s

LReplicaNextProcessAppStateSupply(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_AppStateSupply"
    /\ LET opn_state_supply == received_packet.msg.opn_state_supply
          src_valid == received_packet.src \in s.executor.constants.all.config.replica_ids
          op_valid == opn_state_supply > s.executor.ops_complete
       IN
       IF /\ src_valid
          /\ op_valid
       THEN
          /\ LLearnerForgetOperationsBefore(s.learner, s_next.learner, opn_state_supply)
          /\ LExecutorProcessAppStateSupply(s.executor, s_next.executor, received_packet)
          /\ sent_packets = <<>>
          /\ s_next = [ s EXCEPT !.learner = s_next.learner, !.executor = s_next.executor ]
       ELSE
          /\ s_next = s
          /\ sent_packets = <<>>

LReplicaNextProcessAppStateRequest(s, s_next, received_packet, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_AppStateRequest"
    /\ LExecutorProcessAppStateRequest(s.executor, s_next.executor, received_packet, sent_packets)
    /\ s_next = [ s EXCEPT !.executor = s_next.executor ]

LReplicaNextProcessHeartbeat(s, s_next, received_packet, clock, sent_packets) ==
    /\ received_packet.msg.type = "RslMessage_Heartbeat"
    /\ LProposerProcessHeartbeat(s.proposer, s_next.proposer, received_packet, clock)
    /\ LAcceptorProcessHeartbeat(s.acceptor, s_next.acceptor, received_packet)
    /\ sent_packets = <<>>
    /\ s_next = [ s EXCEPT !.proposer = s_next.proposer, !.acceptor = s_next.acceptor ]


LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s_next, sent_packets) ==
    /\ LProposerMaybeEnterNewViewAndSend1a(s.proposer, s_next.proposer, sent_packets)
    /\ s_next = [ s EXCEPT !.proposer = s_next.proposer ]

LReplicaNextSpontaneousMaybeEnterPhase2(s, s_next, sent_packets) ==
    /\ LProposerMaybeEnterPhase2(s.proposer, s_next.proposer, s.acceptor.log_truncation_point, sent_packets)
    /\ s_next = [ s EXCEPT !.proposer = s_next.proposer ]

LReplicaNextReadClockMaybeNominateValueAndSend2a(s, s_next, clock, sent_packets) ==
    /\ LProposerMaybeNominateValueAndSend2a(s.proposer, s_next.proposer, clock.t, s.acceptor.log_truncation_point, sent_packets)
    /\ s_next = [ s EXCEPT !.proposer = s_next.proposer ]

LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s_next, sent_packets) ==
    \E opn : opn \in s.acceptor.last_checkpointed_operation
        /\ IsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config)
        /\ IF opn > s.acceptor.log_truncation_point
           THEN
              /\ LAcceptorTruncateLog(s.acceptor, s_next.acceptor, opn)
              /\ s_next = [ s EXCEPT !.acceptor = s_next.acceptor ]
              /\ sent_packets = <<>>
           ELSE
              /\ s_next = s
              /\ sent_packets = <<>>

LReplicaNextSpontaneousMaybeMakeDecision(s, s_next, sent_packets) ==
    LET opn == s.executor.ops_complete IN
        IF /\ s.executor.next_op_to_execute.type = "OutstandingOpUnknown"
           /\ opn \in DOMAIN s.learner.unexecuted_learner_state
           /\ Cardinality(s.learner.unexecuted_learner_state[opn].received_2b_message_senders) 
              >= LMinQuorumSize(s.learner.constants.all.config)
        THEN
           /\ LExecutorGetDecision(s.executor, s_next.executor, s.learner.max_ballot_seen, opn,
                                   s.learner.unexecuted_learner_state[opn].candidate_learned_value)
           /\ s_next = [ s EXCEPT !.executor = s_next.executor ]
           /\ sent_packets = <<>>
        ELSE
           /\ s_next = s
           /\ sent_packets = <<>>


LReplicaNextSpontaneousMaybeExecute(s, s_next, sent_packets) ==
    IF /\ s.executor.next_op_to_execute.type = "OutstandingOpKnown"
       /\ s.executor.ops_complete < s.executor.constants.all.params.max_integer_val
       /\ LReplicaConstantsValid(s.executor.constants)
    THEN
       LET v == s.executor.next_op_to_execute.v IN
           /\ LProposerResetViewTimerDueToExecution(s.proposer, s_next.proposer, v)
           /\ LLearnerForgetDecision(s.learner, s_next.learner, s.executor.ops_complete)
           /\ LExecutorExecute(s.executor, s_next.executor, sent_packets)
           /\ s_next = [ s EXCEPT !.proposer = s_next.proposer, 
                                  !.learner = s_next.learner, 
                                  !.executor = s_next.executor ]
    ELSE
       /\ s_next = s
       /\ sent_packets = <<>>

LReplicaNextReadClockMaybeSendHeartbeat(s, s_next, clock, sent_packets) ==
    IF clock.t < s.nextHeartbeatTime
    THEN
        /\ s_next = s
        /\ sent_packets = <<>>
    ELSE
        LET new_next_heartbeat == UpperBoundedAddition(clock.t, 
                                                       s.constants.all.params.heartbeat_period, 
                                                       s.constants.all.params.max_integer_val)
        IN
        /\ s_next = [ s EXCEPT !.nextHeartbeatTime = new_next_heartbeat ]
        /\ sent_packets = LBroadcastToEveryone(
                            s.constants.all.config, 
                            s.constants.my_index,
                            [ type |-> "RslMessage_Heartbeat",
                              bal_heartbeat |-> s.proposer.election_state.current_view,
                              suspicious |-> (s.constants.my_index \in s.proposer.election_state.current_view_suspectors),
                              opn_ckpt |-> s.executor.ops_complete ],
                            sent_packets)                                         

LReplicaNextReadClockCheckForViewTimeout(s, s_next, clock, sent_packets) ==
    /\ LProposerCheckForViewTimeout(s.proposer, s_next.proposer, clock.t)
    /\ sent_packets = <<>>
    /\ s_next = [ s EXCEPT !.proposer = s_next.proposer ]

LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s_next, clock, sent_packets) ==
    /\ LProposerCheckForQuorumOfViewSuspicions(s.proposer, s_next.proposer, clock.t)
    /\ sent_packets = <<>>
    /\ s_next = [ s EXCEPT !.proposer = s_next.proposer ]

====
