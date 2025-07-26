include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Constants.i.dfy"
include "Broadcast.i.dfy"
include "Election.i.dfy"
include "Acceptor.i.dfy"
include "CheckValSafety.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"

module LiveByzRSL__Proposer_i {
    import opened LiveByzRSL__Configuration_i
    import opened LiveByzRSL__Environment_i
    import opened LiveByzRSL__Constants_i
    import opened LiveByzRSL__Broadcast_i
    import opened LiveByzRSL__Acceptor_i
    import opened LiveByzRSL__Election_i
    import opened LiveByzRSL__Types_i
    import opened LiveByzRSL__Message_i
    import opened LiveByzRSL__CheckValSafety_i
    import opened Concrete_NodeIdentity_i
    import opened Common__UpperBound_s
    import opened Collections__CountMatches_i

    // datatype ProposerTuple = ProposedrTuple(received_1b_message_sender:set<NodeIdentity>, msg1bs:seq<RslMessage>)

    datatype IncompleteBatchTimer = IncompleteBatchTimerOn(when:int) | IncompleteBatchTimerOff()

    datatype LProposer = LProposer(
        constants:LReplicaConstants,
        // The replica constants, duplicated here for convenience

        current_state:int,
        // What state the proposer is in:
        // 0 = not leader
        // 1 = leader in phase 1
        // 2 = leader in phase 2

        // request_queue:RequestBatch,
        request_queue:seq<Request>,
        // Values that clients have requested that I need to eventually
        // propose, in the order I should propose them

        max_ballot_i_sent_1a:Ballot,
        // The maximum ballot I've sent a 1a message for

        next_operation_number_to_propose:int,
        // The next operation number I should propose

        // received_1b_packets:set<RslPacket>,
        // received_1b_packets:ProposerTuple,
        received_1b_packets:seq<RslPacket>,
        // The set of 1b messages I've received concerning max_ballot_i_sent_1a

        highest_seqno_requested_by_client_this_view:map<NodeIdentity, int>,
        // For each client, the highest sequence number for a request
        // I proposed in max_ballot_i_sent_1a

        incomplete_batch_timer:IncompleteBatchTimer,
        // If the incomplete batch timer is set, it indicates when I should
        // give up on trying to amass a full-size batch and just propose
        // whatever I have.  If it's not set, I shouldn't propose an
        // incomplete batch.

        election_state:ElectionState
        // State for view change election management
    )

    // predicate ProposerTupleMatch(tup:ProposerTuple, constants:LReplicaConstants)
    // {
    //     && |tup.packets| == |constants.all.config.replica_ids|
    //     && (forall idx :: idx in tup.indices ==> 
    //             && 0 <= idx < |constants.all.config.replica_ids|
    //             && tup.packets[idx].Received? 
    //             && tup.packets[idx].p.msg.RslMessage_1b?)
    //     && (forall idx :: 0 <= idx < |constants.all.config.replica_ids| && tup.packets[idx].Received? ==> 
    //                     idx in tup.indices)
    //     && (forall idx :: 0 <= idx < |constants.all.config.replica_ids| && tup.packets[idx].UnReceived? ==> 
    //                     idx !in tup.indices)
    // }

    // function ConvertProposerTupleToReceived1bMsga(tup:ProposerTuple, constants:LReplicaConstants) : seq<RslMessage>
    //     requires LSetOfMessage1b(tup)
    //     // requires ProposerTupleMatch(tup, constants)
    //     ensures forall m :: m in ConvertProposerTupleToReceived1bMsga(tup, constants) ==> m.RslMessage_1b?
    //     // ensures |tup.indices| == |ConvertProposerTupleToReceived1bMsga(tup, constants)|
    // {
    //     ConvertProposerTupleToReceived1bMsgaHelper(tup.packets)
    // }

    // function ConvertProposerTupleToReceived1bMsgaHelper(packets:seq<Received1b>) : seq<RslMessage>
    //     requires (forall r :: r in packets && r.Received? ==> r.p.msg.RslMessage_1b?)
    //     ensures (forall m :: m in ConvertProposerTupleToReceived1bMsgaHelper(packets) ==> m.RslMessage_1b?)
    // {
    //     if |packets| == 0 then
    //         []
    //     else
    //         ConvertProposerTupleToReceived1bMsgaHelper(packets[1..]) + if packets[0].Received? then [packets[0].p.msg] else []
    // }

    // predicate LSetOfMessage1b(tup:ProposerTuple)
    // {
    //     // forall p :: p in tup.packets ==> p.msg.RslMessage_1b?
    //     // forall idx :: idx in tup.indices ==> tup.packets[idx].Received? && tup.packets[idx].p.msg.RslMessage_1b?
    //     forall r :: r in tup.packets && r.Received? ==> r.p.msg.RslMessage_1b?
    // }

    // predicate LSetOfMessage1bAboutBallot(tup:ProposerTuple, b:Ballot)
    // {
    //     && LSetOfMessage1b(tup)
    //     // && (forall p :: p in tup.packets ==> p.msg.bal_1b == b)
    //     // && (forall idx :: idx in tup.indices ==> tup.packets[idx].p.msg.bal_1b == b)
    //     && (forall r :: r in tup.packets && r.Received? ==> r.p.msg.bal_1b == b)
    // }

    // predicate LAllAcceptorsHadNoProposal(tup:ProposerTuple, opn:OperationNumber)
    //     requires LSetOfMessage1b(tup)
    // {
    //     // forall p :: p in tup.packets ==> !(opn in p.msg.votes)
    //     // forall idx :: idx in tup.indices ==> !(opn in tup.packets[idx].p.msg.votes)
    //     (forall r :: r in tup.packets && r.Received? ==> !(opn in r.p.msg.votes))
    // }

    // predicate LIsAfterLogTruncationPoint(opn:OperationNumber, tup:ProposerTuple)
    // {
    //     // (forall p :: p in tup.packets && p.msg.RslMessage_1b? ==> p.msg.log_truncation_point <= opn)
    //     && LSetOfMessage1b(tup)
    //     // && (forall idx :: idx in tup.indices ==> tup.packets[idx].p.msg.log_truncation_point <= opn)
    //     && (forall r :: r in tup.packets && r.Received? ==> r.p.msg.log_truncation_point <= opn)
    // }

    // predicate LProposerCanNominateUsingOperationNumber(s:LProposer, log_truncation_point:OperationNumber, opn:OperationNumber)
    // {
    //     && s.election_state.current_view == s.max_ballot_i_sent_1a
    //     && s.current_state == 2
    //     && |s.received_1b_packets.indices| >= LByzQuorumSize(s.constants.all.config)
    //     && LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
    //     // Don't try to nominate for an operation that's already been truncated into history:
    //     && LIsAfterLogTruncationPoint(opn, s.received_1b_packets)
    //     // Don't try to nominate in an operation that's too far in the future; that would grow the log too much.
    //     && opn < UpperBoundedAddition(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val)
    //     // Disallow negative operations
    //     && opn >= 0
    //     // It must be possible to add one and still be representable, so we can compute next_operation_number_to_propose
    //     && LtUpperBound(opn, s.constants.all.params.max_integer_val)
    // }

    function FindTheLowestTruncatePoint(S:seq<RslPacket>) : OperationNumber
        requires LSeqOfMessage1b(S)
    {
        if |S| == 0 then
            0
        else
            var opn := FindTheLowestTruncatePoint(S[1..]);
            if opn > 0 && opn < S[0].msg.log_truncation_point then opn else S[0].msg.log_truncation_point
    }
    

    predicate LIsAfterLogTruncationPoint(opn:OperationNumber, S:seq<RslPacket>)
    {
        (forall p :: p in S && p.msg.RslMessage_1b? ==> p.msg.log_truncation_point <= opn)
    }

    predicate LProposerCanNominateUsingOperationNumber(s:LProposer, log_truncation_point:OperationNumber, opn:OperationNumber)
    {
        && s.election_state.current_view == s.max_ballot_i_sent_1a
        && s.current_state == 2
        && |s.received_1b_packets| >= LByzQuorumSize(s.constants.all.config)
        && LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
        // Don't try to nominate for an operation that's already been truncated into history:
        && LIsAfterLogTruncationPoint(opn, s.received_1b_packets)
        // Don't try to nominate in an operation that's too far in the future; that would grow the log too much.
        && opn < UpperBoundedAddition(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val)
        // Disallow negative operations
        && opn >= 0
        // It must be possible to add one and still be representable, so we can compute next_operation_number_to_propose
        && LtUpperBound(opn, s.constants.all.params.max_integer_val)
    }

    // predicate LSetOfMessage1b(tup:ProposerTuple)
    // {
    //     forall m :: m in tup.msg1bs ==> m.RslMessage_1b?
    // }

    // predicate LSetOfMessage1bAboutBallot(tup:ProposerTuple, b:Ballot)
    // {
    //     && LSetOfMessage1b(tup)
    //     && (forall m :: m in tup.msg1bs ==> m.bal_1b == b)
    // }

    // predicate LAllAcceptorsHadNoProposal(tup:ProposerTuple, opn:OperationNumber)
    //     requires LSetOfMessage1b(tup)
    // {
    //     forall m :: m in tup.msg1bs ==> !(opn in m.votes)
    // }

    // predicate LIsAfterLogTruncationPoint(opn:OperationNumber, tup:ProposerTuple)
    // {
    //     (forall m :: m in tup.msg1bs && m.RslMessage_1b? ==> m.log_truncation_point <= opn)
    // }

    // predicate LProposerCanNominateUsingOperationNumber(s:LProposer, log_truncation_point:OperationNumber, opn:OperationNumber)
    // {
    //     && s.election_state.current_view == s.max_ballot_i_sent_1a
    //     && s.current_state == 2
    //     && |s.received_1b_packets.received_1b_message_sender| >= LByzQuorumSize(s.constants.all.config)
    //     && LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
    //     // Don't try to nominate for an operation that's already been truncated into history:
    //     && LIsAfterLogTruncationPoint(opn, s.received_1b_packets)
    //     // Don't try to nominate in an operation that's too far in the future; that would grow the log too much.
    //     && opn < UpperBoundedAddition(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val)
    //     // Disallow negative operations
    //     && opn >= 0
    //     // It must be possible to add one and still be representable, so we can compute next_operation_number_to_propose
    //     && LtUpperBound(opn, s.constants.all.params.max_integer_val)
    // }

    predicate LProposerInit(s:LProposer, c:LReplicaConstants)
        requires WellFormedLConfiguration(c.all.config)
    {
        // var received1bs := seq(|c.all.config.replica_ids|, i => UnReceived());
        
        && s.constants == c
        && s.current_state == 0
        && s.request_queue == []
        && s.max_ballot_i_sent_1a == Ballot(0, c.my_index)
        && s.next_operation_number_to_propose == 0
        // && s.received_1b_packets == ProposerTuple({}, received1bs)
        && s.received_1b_packets == []
        && s.highest_seqno_requested_by_client_this_view == map[]
        && ElectionStateInit(s.election_state, c)
        && s.incomplete_batch_timer == IncompleteBatchTimerOff()
    }

    // predicate LProposerInit(s:LProposer, c:LReplicaConstants)
    //     requires WellFormedLConfiguration(c.all.config)
    // {
    //     && s.constants == c
    //     && s.current_state == 0
    //     && s.request_queue == []
    //     && s.max_ballot_i_sent_1a == Ballot(0, c.my_index)
    //     && s.next_operation_number_to_propose == 0
    //     && s.received_1b_packets == ProposerTuple({}, [])
    //     && s.highest_seqno_requested_by_client_this_view == map[]
    //     && ElectionStateInit(s.election_state, c)
    //     && s.incomplete_batch_timer.IncompleteBatchTimerOff?
    // }

    predicate LProposerProcessRequest(s:LProposer, s':LProposer, packet:RslPacket)
        requires packet.msg.RslMessage_Request?
    {
        var val := Request(packet.src, packet.msg.seqno_req, packet.msg.val);
        && ElectionStateReflectReceivedRequest(s.election_state, s'.election_state, val)
        && if && s.current_state != 0
            && (|| val.client !in s.highest_seqno_requested_by_client_this_view
                || val.seqno > s.highest_seqno_requested_by_client_this_view[val.client]) then
            s' == s.(election_state := s'.election_state,
            request_queue := s.request_queue + [val],
            highest_seqno_requested_by_client_this_view := s.highest_seqno_requested_by_client_this_view[val.client := val.seqno])
        else
            s' == s.(election_state := s'.election_state)
    }

    predicate LProposerMaybeEnterNewViewAndSend1a(s:LProposer, s':LProposer, sent_packets:seq<RslPacket>)
    {
        if  && s.election_state.current_view.proposer_id == s.constants.my_index
            && BalLt(s.max_ballot_i_sent_1a, s.election_state.current_view) then
            && s' == s.(current_state := 1,
                    max_ballot_i_sent_1a := s.election_state.current_view,
                    // received_1b_packets := ProposerTuple({}, []),
                    received_1b_packets := [],
                    highest_seqno_requested_by_client_this_view := map[],
                    request_queue := s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch)
            && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, RslMessage_1a(s.election_state.current_view), sent_packets)
        else
            s' == s && sent_packets == []
    }

    predicate LProposerProcess1b(s:LProposer, s':LProposer, p:RslPacket)
        requires p.msg.RslMessage_1b?
        requires p.src in s.constants.all.config.replica_ids
        requires p.msg.bal_1b == s.max_ballot_i_sent_1a
        requires s.current_state == 1
        // requires ProposerTupleMatch(s.received_1b_packets, s.constants)
        requires forall other_packet :: other_packet in s.received_1b_packets ==> other_packet.src != p.src
    {
        s' == s.(received_1b_packets := s.received_1b_packets + [p])
    }

    // predicate LProposerProcess1b(s:LProposer, s':LProposer, p:RslPacket)
    //     requires p.msg.RslMessage_1b?
    //     requires p.src in s.constants.all.config.replica_ids
    //     requires p.msg.bal_1b == s.max_ballot_i_sent_1a
    //     requires s.current_state == 1
    //     requires forall other_packet :: other_packet in s.received_1b_packets.received_1b_message_sender ==> other_packet != p.src
    // {
    //     var tup := s.received_1b_packets;
    //     var new_tup := tup.(received_1b_message_sender := tup.received_1b_message_sender + {p.src}, 
    //                         msg1bs := tup.msg1bs + [p.msg]);
    //     s' == s.(received_1b_packets := new_tup)
    // }

    predicate LProposerMaybeEnterPhase2(s:LProposer, s':LProposer, log_truncation_point:OperationNumber, sent_packets:seq<RslPacket>)
    {
        if  && |s.received_1b_packets| >= LByzQuorumSize(s.constants.all.config)
            && LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
            && s.current_state == 1 then
            // var opn := FindTheLowestTruncatePoint(s.received_1b_packets);
            && s' == s.(current_state := 2,
                    next_operation_number_to_propose := 
                    // opn)
                    log_truncation_point) // 为什么要从truncate point开始propose？
            && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                    RslMessage_StartingPhase2(s.max_ballot_i_sent_1a, log_truncation_point), sent_packets)
        else
            s' == s && sent_packets == []
    }

    // predicate LProposerMaybeEnterPhase2(s:LProposer, s':LProposer, log_truncation_point:OperationNumber, sent_packets:seq<RslPacket>)
    // {
    //     if  && |s.received_1b_packets.received_1b_message_sender| >= LByzQuorumSize(s.constants.all.config)
    //         && LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
    //         && s.current_state == 1 then
    //         && s' == s.(current_state := 2,
    //                 next_operation_number_to_propose := log_truncation_point) // 为什么要从truncate point开始propose？
    //         && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
    //                                 RslMessage_StartingPhase2(s.max_ballot_i_sent_1a, log_truncation_point), sent_packets)
    //     else
    //         s' == s && sent_packets == []
    // }

    predicate LProposerNominateNewValueAndSend1c(s:LProposer, s':LProposer, clock:int, log_truncation_point:OperationNumber,
                                                sent_packets:seq<RslPacket>)
        requires LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
        requires LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    {
        var batchSize := if |s.request_queue| <= s.constants.all.params.max_batch_size || s.constants.all.params.max_batch_size < 0 then
                        |s.request_queue|
                        else
                        s.constants.all.params.max_batch_size;
        var v := s.request_queue[..batchSize];
        var opn := s.next_operation_number_to_propose;
        // var msg1bs := Convert1bPacketsSeqToMsgSeq(s.received_1b_packets);
        && s' == s.(request_queue := s.request_queue[batchSize..],
                next_operation_number_to_propose := s.next_operation_number_to_propose + 1,
                incomplete_batch_timer := if |s.request_queue| > batchSize then IncompleteBatchTimerOn(UpperBoundedAddition(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)) else IncompleteBatchTimerOff())
        && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, RslMessage_1c(s.max_ballot_i_sent_1a, opn, v/*, msg1bs*/), sent_packets)
    }

    predicate LProposerNominateOldValueAndSend1c(s:LProposer, s':LProposer, log_truncation_point:OperationNumber, sent_packets:seq<RslPacket>)
        requires LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
        requires !LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    {
        var opn := s.next_operation_number_to_propose;
        var byzq := LByzQuorumSize(s.constants.all.config);
        var wq := LMinQuorumSize(s.constants.all.config);
        // var msg1bs := Convert1bPacketsSeqToMsgSeq(s.received_1b_packets);
        if exists p ::
            p in s.received_1b_packets && opn in p.msg.votes 
            && LValIsSafeAt(p.msg.votes[opn].max_val, /*s.max_ballot_i_sent_1a,*/ s.received_1b_packets, opn, byzq, wq) 
        then 
            var p :| p in s.received_1b_packets && opn in p.msg.votes 
            && LValIsSafeAt(p.msg.votes[opn].max_val, /*s.max_ballot_i_sent_1a,*/ s.received_1b_packets, opn, byzq, wq);
            && s' == s.(next_operation_number_to_propose := s.next_operation_number_to_propose + 1)
            && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, RslMessage_1c(s.max_ballot_i_sent_1a, opn, p.msg.votes[opn].max_val/*, msg1bs*/), sent_packets)
        else
            // s' == s.(next_operation_number_to_propose := s.next_operation_number_to_propose + 1) 
            s' == s
            && sent_packets == []
    }

    predicate LProposerMaybeNominateValueAndSend1c(s:LProposer, s':LProposer, clock:int, log_truncation_point:int, sent_packets:seq<RslPacket>)
    {
        if !LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose) then
            s' == s && sent_packets == []
        else if !LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose) then
            LProposerNominateOldValueAndSend1c(s, s', log_truncation_point, sent_packets)
        else if
            // LExistsAcceptorHasProposalLargeThanOpn(s.received_1b_packets, s.next_operation_number_to_propose)
            || |s.request_queue| >= s.constants.all.params.max_batch_size
            || (|s.request_queue| > 0 && s.incomplete_batch_timer.IncompleteBatchTimerOn? && clock >= s.incomplete_batch_timer.when) then
            LProposerNominateNewValueAndSend1c(s, s', clock, log_truncation_point, sent_packets)
        else if |s.request_queue| > 0 && s.incomplete_batch_timer.IncompleteBatchTimerOff? then
            && s' == s.(incomplete_batch_timer := IncompleteBatchTimerOn(UpperBoundedAddition(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)))
            && sent_packets == []
        else
            s' == s && sent_packets == []
    }

    predicate LProposerProcessHeartbeat(s:LProposer, s':LProposer, p:RslPacket, clock:int)
        requires p.msg.RslMessage_Heartbeat?
    {
        && ElectionStateProcessHeartbeat(s.election_state, s'.election_state, p, clock)
        // mode checking
        && (if BalLt(s.election_state.current_view, s'.election_state.current_view) then
            s'.current_state == 0 && s'.request_queue == []
        else
            s'.current_state == s.current_state && s'.request_queue == s.request_queue
            )
        && s' == s.(election_state := s'.election_state,
                current_state := s'.current_state,
                request_queue := s'.request_queue)
    }

    predicate LProposerCheckForViewTimeout(s:LProposer, s':LProposer, clock:int)
    {
        && ElectionStateCheckForViewTimeout(s.election_state, s'.election_state, clock)
        && s' == s.(election_state := s'.election_state)
    }

    predicate LProposerCheckForQuorumOfViewSuspicions(s:LProposer, s':LProposer, clock:int)
    {
        && ElectionStateCheckForQuorumOfViewSuspicions(s.election_state, s'.election_state, clock)
        && (if BalLt(s.election_state.current_view, s'.election_state.current_view) then
            s'.current_state == 0 && s'.request_queue == []
        else
            s'.current_state == s.current_state && s'.request_queue == s.request_queue
            )
        && s' == s.(election_state := s'.election_state,
                current_state := s'.current_state,
                request_queue := s'.request_queue)
    }

    predicate LProposerResetViewTimerDueToExecution(s:LProposer, s':LProposer, val:RequestBatch)
    {
        && ElectionStateReflectExecutedRequestBatch(s.election_state, s'.election_state, val)
        && s' == s.(election_state := s'.election_state)
    }

}