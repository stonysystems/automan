include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "ClockReading.i.dfy"
include "Constants.i.dfy"
include "Proposer.i.dfy"
include "Acceptor.i.dfy"
include "Learner.i.dfy"
include "Executor.i.dfy"

module LiveByzRSL__Replica_i {
    import opened LiveByzRSL__Configuration_i
    import opened LiveByzRSL__Environment_i
    import opened LiveByzRSL__Types_i
    import opened LiveByzRSL__ClockReading_i
    import opened LiveByzRSL__Constants_i
    import opened LiveByzRSL__Proposer_i
    import opened LiveByzRSL__Acceptor_i
    import opened LiveByzRSL__Learner_i
    import opened LiveByzRSL__Election_i
    import opened LiveByzRSL__Executor_i
    import opened LiveByzRSL__Broadcast_i
    import opened LiveByzRSL__Message_i
    import opened LiveByzRSL__CheckValSafety_i
    import opened Common__UpperBound_s
    import opened Collections__CountMatches_i
    import opened Environment_s

    datatype LReplica = LReplica(
        constants:LReplicaConstants,
        nextHeartbeatTime:int,
        proposer:LProposer,
        acceptor:LAcceptor,
        learner:LLearner,
        executor:LExecutor)

    predicate LReplicaInit(r:LReplica, c:LReplicaConstants)
        requires WellFormedLConfiguration(c.all.config)
    {
        && r.constants == c
        && r.nextHeartbeatTime == 0
        && LProposerInit(r.proposer, c)
        && LAcceptorInit(r.acceptor, c)
        && LLearnerInit(r.learner, c)
        && LExecutorInit(r.executor, c)
    }

    predicate LReplicaNextProcessInvalid(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_Invalid?
    {
        && s' == s
        && sent_packets == []
    }

    predicate LReplicaNextProcessRequest(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_Request?
    {
        if  && received_packet.src in s.executor.reply_cache
            && s.executor.reply_cache[received_packet.src].Reply?
            && received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno then
            && LExecutorProcessRequest(s.executor, received_packet, sent_packets)
            && s' == s
        else
            && LProposerProcessRequest(s.proposer, s'.proposer, received_packet)
            && sent_packets == []
            && s' == s.(proposer := s'.proposer)
    }

    predicate LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    {
        && LProposerMaybeEnterNewViewAndSend1a(s.proposer, s'.proposer, sent_packets)
        && LAcceptorMaybeEnterNewView(s.acceptor, s'.acceptor)
        && s' == s.(proposer := s'.proposer, acceptor := s'.acceptor)
    }

    predicate LReplicaNextProcess1a(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_1a?
    {
        && LAcceptorProcess1a(s.acceptor, s'.acceptor, received_packet, sent_packets)
        // UNCHANGED
        && s' == s.(acceptor := s'.acceptor)
    }

    predicate LReplicaNextProcess1b(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_1b?
    {
        if  && received_packet.src in s.proposer.constants.all.config.replica_ids
            && received_packet.msg.bal_1b == s.proposer.max_ballot_i_sent_1a
            && s.proposer.current_state == 1
            && (forall other_packet :: other_packet in s.proposer.received_1b_packets ==> other_packet.src != received_packet.src) then
            && LProposerProcess1b(s.proposer, s'.proposer, received_packet)
            && LAcceptorTruncateLog(s.acceptor, s'.acceptor, received_packet.msg.log_truncation_point)
            && sent_packets == []
            && s' == s.(proposer := s'.proposer, acceptor := s'.acceptor)
        else if && received_packet.src in s.acceptor.constants.all.config.replica_ids
                && (forall other_packet :: other_packet in s.acceptor.received_1b_packets ==> other_packet.src != received_packet.src) then
            && LAcceptorProcess1b(s.acceptor, s'.acceptor, received_packet)
            && s' == s.(acceptor := s'.acceptor) && sent_packets == []
        else 
            s' == s && sent_packets == []
    }

    predicate LReplicaNextSpontaneousMaybeEnterPhase2(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    {
        && LProposerMaybeEnterPhase2(s.proposer, s'.proposer, s.acceptor.log_truncation_point, sent_packets)
        && s' == s.(proposer := s'.proposer)
    }

    predicate LReplicaNextProcessStartingPhase2(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_StartingPhase2?
    {
        && LExecutorProcessStartingPhase2(s.executor, s'.executor, received_packet, sent_packets)
        && s' == s.(executor := s'.executor)
    }

    predicate LReplicaNextReadClockMaybeNominateValueAndSend1c(s:LReplica, s':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
    {
        && LProposerMaybeNominateValueAndSend1c(s.proposer, s'.proposer, clock.t, s.acceptor.log_truncation_point, sent_packets)
        && s' == s.(proposer := s'.proposer)
    }

    predicate LReplicaNextProcess1c(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_1c?
    {
        var m := received_packet.msg;
        var packets_1b := s.acceptor.received_1b_packets;
        // var msgs_1b := Convert1bPacketsSeqToMsgSeq(packets_1b);
        var byzq := LByzQuorumSize(s.constants.all.config);
        var wq := LMinQuorumSize(s.constants.all.config);
        var req_is_valid_from_client := forall req :: req in m.val_1c ==> CheckRequestValid(s.proposer.election_state, req);
        var req_is_safe := 
            if s.proposer.current_state == 2 then
                true
            else 
                if LSeqOfMessage1b(packets_1b) then
                // var msgs_1b := Convert1bPacketsSeqToMsgSeq(packets_1b); 
                (|| LAllAcceptorsHadNoProposal(packets_1b, m.opn_1c)
                 || LValIsSafeAt(m.val_1c, packets_1b, m.opn_1c, byzq, wq))
            else
                false;
        if  && received_packet.src in s.acceptor.constants.all.config.replica_ids
            && req_is_valid_from_client
            && req_is_safe
            && BalLeq(s.acceptor.max_bal, m.bal_1c)
            && LeqUpperBound(m.opn_1c, s.acceptor.constants.all.params.max_integer_val) then
            && LAcceptorProcess1c(s.acceptor, s'.acceptor, received_packet, sent_packets)
            && s' == s.(acceptor := s'.acceptor)
        else
            s' == s && sent_packets == []
    }

    predicate LReplicaNextProcess2av(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_2av?
    {
        // s' == s && sent_packets == []
        var opn := received_packet.msg.opn_2av;
        var src := received_packet.src;
        var op_sendable := s.acceptor.opn_to_be_send_2b < opn || (s.acceptor.opn_to_be_send_2b == opn && s.acceptor.val_to_be_sent_2b.ValToBeSent2bUnknown?);
        if && op_sendable 
           && src in s.acceptor.constants.all.config.replica_ids
        //    && AcceptorStateCorrect(s.acceptor.received_2avs, s.acceptor.max_bal, s.acceptor.constants.all.config) 
        then
            && LAcceptorProcess2av(s.acceptor, s'.acceptor, received_packet)
            && s' == s.(acceptor := s'.acceptor)
            && sent_packets == []
        else
            && s' == s
            && sent_packets == []
    }

    // predicate LReplicaNextSpontaneousMaybeDecide2bVal(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    // {
    //     var opn := s.acceptor.opn_to_be_send_2b;
    //     var quorum := LByzQuorumSize(s.acceptor.constants.all.config);
    //     if && s.acceptor.val_to_be_sent_2b.ValToBeSent2bUnknown?
    //        && opn in s.acceptor.received_2avs
    //        && |s.acceptor.received_2avs[opn].received_2av_packets| >= quorum
    //        && AcceptorStateCorrect(s.acceptor.received_2avs, s.acceptor.max_bal, s.constants.all.config)
    //     //    && (forall opn :: opn in s.acceptor.received_2avs ==> forall p :: p in s.acceptor.received_2avs[opn].received_2av_packets ==> p.msg.RslMessage_2av?)
    //        && HasReceivedSame2avFromByzQuorum(s.acceptor.received_2avs[opn], quorum)  
    //     then
    //         exists p :: 
    //             && p in s.acceptor.received_2avs[opn].received_2av_packets
    //             && CountMatchedValInReceived2avs(s.acceptor.received_2avs[opn].received_2av_packets, p.msg.val_2av) >= quorum
    //             && LAcceptorDecide2bVal(s.acceptor, s'.acceptor, s.acceptor.max_bal, opn, p.msg.val_2av)
    //         // && LAcceptorDecide2bVal(s.acceptor, s'.acceptor)
    //         && s' == s.(acceptor := s'.acceptor)
    //         && sent_packets == []
            
    //     else
    //         s' == s && sent_packets == []
    //     // && s' == s.(acceptor := s'.acceptor)
    //     // var opn := s.acceptor.opn_to_be_send_2b;
    //     // if  && opn in s.acceptor.received_2avs
    //     //     && |s.acceptor.received_2avs[opn].received_2av_message_senders| >= LByzQuorumSize(s.learner.constants.all.config) then
    //     //     && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn,
    //     //                         s.learner.unexecuted_learner_state[opn].candidate_learned_value)
    //     //     && s' == s.(executor := s'.executor)
    //     //     && sent_packets == []
    //     // else
    //     //     s' == s && sent_packets == []
    // }

    // predicate LReplicaNextSpontaneousMaybeDecide2bVal(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    // {
    //     var opn := s.acceptor.opn_to_be_send_2b;
    //     var quorum := LByzQuorumSize(s.acceptor.constants.all.config);
    //     if && s.acceptor.val_to_be_sent_2b.ValToBeSent2bUnknown?
    //        && opn in s.acceptor.received_2avs
    //        && |s.acceptor.received_2avs[opn].received_2av_packets| >= quorum
    //        && AcceptorStateCorrect(s.acceptor.received_2avs, s.acceptor.max_bal, s.constants.all.config)
    //     //    && (forall opn :: opn in s.acceptor.received_2avs ==> forall p :: p in s.acceptor.received_2avs[opn].received_2av_packets ==> p.msg.RslMessage_2av?)
    //        && HasReceivedSame2avFromByzQuorum(s.acceptor.received_2avs[opn], quorum)  
    //     then
    //         if exists p :: 
    //             && p in s.acceptor.received_2avs[opn].received_2av_packets
    //             && CountMatchedValInReceived2avs(s.acceptor.received_2avs[opn].received_2av_packets, p.msg.val_2av) >= quorum
    //         then
    //             var p :|  p in s.acceptor.received_2avs[opn].received_2av_packets
    //             && CountMatchedValInReceived2avs(s.acceptor.received_2avs[opn].received_2av_packets, p.msg.val_2av) >= quorum;

    //             && LAcceptorDecide2bVal(s.acceptor, s'.acceptor, s.acceptor.max_bal, opn, p.msg.val_2av)
    //             // && LAcceptorDecide2bVal(s.acceptor, s'.acceptor)
    //             && s' == s.(acceptor := s'.acceptor)
    //             && sent_packets == []
    //         else
    //             s' == s && sent_packets == []
    //     else
    //         s' == s && sent_packets == []
    // }


    predicate LReplicaNextSpontaneousMaybeSend2b(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    {
        if && s.acceptor.val_to_be_sent_2b.ValToBeSent2bKnown? 
           && s.acceptor.val_to_be_sent_2b.bal == s.acceptor.max_bal
        then
            && LAcceptorSent2b(s.acceptor, s'.acceptor, sent_packets)
            && s' == s.(acceptor := s'.acceptor)
        else
            s' == s && sent_packets== []
    }

    // predicate LReplicaNextSpontaneousMaybeSend2b(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    // {
    //     var opn := s.acceptor.opn_to_be_send_2b;
    //     var quorum := LByzQuorumSize(s.acceptor.constants.all.config);
    //     if && opn in s.acceptor.received_2avs
    //        && |s.acceptor.received_2avs[opn].received_2av_message_senders| >= quorum
    //        && IsByzQuorumSendSame2av(s.acceptor.received_2avs[opn].candidate_value, quorum) 
    //        && Received2avsAreValid(s.acceptor, opn) then
    //         && LAcceptorMaybeSent2b(s.acceptor, s'.acceptor, sent_packets)
    //         && s' == s.(acceptor := s'.acceptor)
    //     else
    //         s' == s && sent_packets == []
    //     // && s' == s.(acceptor := s'.acceptor)
    //     // var opn := s.acceptor.opn_to_be_send_2b;
    //     // if  && opn in s.acceptor.received_2avs
    //     //     && |s.acceptor.received_2avs[opn].received_2av_message_senders| >= LByzQuorumSize(s.learner.constants.all.config) then
    //     //     && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn,
    //     //                         s.learner.unexecuted_learner_state[opn].candidate_learned_value)
    //     //     && s' == s.(executor := s'.executor)
    //     //     && sent_packets == []
    //     // else
    //     //     s' == s && sent_packets == []
    // }

    predicate LReplicaNextProcess2b(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_2b?
    {
        var opn := received_packet.msg.opn_2b;
        var src := received_packet.src;
        var op_learnable := s.executor.ops_complete < opn || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.OutstandingOpUnknown?);
        if && op_learnable 
           && src in s.learner.constants.all.config.replica_ids
        //    && LearnerStateCorrect(s.learner.unexecuted_learner_state, s.learner.max_ballot_seen, s.learner.constants.all.config) 
        then
            && LLearnerProcess2b(s.learner, s'.learner, received_packet)
            && sent_packets == []
            && s' == s.(learner := s'.learner)
        else
            && s' == s
            && sent_packets == []
    }

    predicate LReplicaNextProcessReply(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_Reply?
    {
        && sent_packets == []
        && s' == s
    }

    predicate LReplicaNextProcessAppStateSupply(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_AppStateSupply?
    {
        if received_packet.src in s.executor.constants.all.config.replica_ids && received_packet.msg.opn_state_supply > s.executor.ops_complete then
            && LLearnerForgetOperationsBefore(s.learner, s'.learner, received_packet.msg.opn_state_supply)
            && LExecutorProcessAppStateSupply(s.executor, s'.executor, received_packet)
            && sent_packets == []
            && s' == s.(learner := s'.learner, executor := s'.executor)
        else
            s' == s && sent_packets == []
    }

    predicate LReplicaNextProcessAppStateRequest(s:LReplica, s':LReplica, received_packet:RslPacket, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_AppStateRequest?
    {
        && LExecutorProcessAppStateRequest(s.executor, s'.executor, received_packet, sent_packets)
        && s' == s.(executor := s'.executor)
    }

    predicate LReplicaNextProcessHeartbeat(s:LReplica, s':LReplica, received_packet:RslPacket, clock:int, sent_packets:seq<RslPacket>)
        requires received_packet.msg.RslMessage_Heartbeat?
    {
        && LProposerProcessHeartbeat(s.proposer, s'.proposer, received_packet, clock)
        && LAcceptorProcessHeartbeat(s.acceptor, s'.acceptor, received_packet)
        && sent_packets == []
        && s' == s.(proposer := s'.proposer, acceptor := s'.acceptor)
    }

    // 是否要调整这个的quorum size?
    predicate LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    {
        exists opn ::
            && opn in s.acceptor.last_checkpointed_operation
            && IsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config)
            && if opn > s.acceptor.log_truncation_point then
                && LAcceptorTruncateLog(s.acceptor, s'.acceptor, opn)
                && s' == s.(acceptor := s'.acceptor)
                && sent_packets == []
            else
                && s' == s
                && sent_packets == []
    }

    // predicate LReplicaNextSpontaneousMaybeMakeDecision(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    // {
    //     var opn := s.executor.ops_complete;
    //     if  && s.executor.next_op_to_execute.OutstandingOpUnknown?
    //         && opn in s.learner.unexecuted_learner_state
    //         && |s.learner.unexecuted_learner_state[opn].received_2bs| >= LMinQuorumSize(s.learner.constants.all.config) then
    //         && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn,
    //                             s.learner.unexecuted_learner_state[opn].candidate_learned_value)
    //         && s' == s.(executor := s'.executor)
    //         && sent_packets == []
    //     else
    //         s' == s && sent_packets == []
    // }

    // predicate LReplicaNextSpontaneousMaybeMakeDecision(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    // {
    //     var opn := s.executor.ops_complete;
    //     var quorum := LMinQuorumSize(s.acceptor.constants.all.config);
    //     if  && s.executor.next_op_to_execute.OutstandingOpUnknown?
    //         && opn in s.learner.unexecuted_learner_state
    //         && LearnerStateCorrect(s.learner.unexecuted_learner_state, s.learner.max_ballot_seen, s.constants.all.config)
    //         && |s.learner.unexecuted_learner_state[opn].received_2bs| >= quorum
    //         // && IsWeakQuorumSendSame2b(s.learner.unexecuted_learner_state[opn].candidate_learned_value, quorum)
    //         && HasReceivedSame2bFromWeakQuorum(s.learner.unexecuted_learner_state[opn], quorum)
    //     then
    //         exists p :: 
    //                 && p in s.learner.unexecuted_learner_state[opn].received_2bs
    //                 && CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, p.msg.val_2b) >= quorum
    //                 && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn, p.msg.val_2b)
    //         // exists v ::
    //         //     v in s.learner.unexecuted_learner_state[opn].candidate_learned_value
    //         //     && CountMatchesInSeq(s.learner.unexecuted_learner_state[opn].candidate_learned_value, x => x == v) >= quorum
    //         //     && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn, v)
    //         // && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn,
    //         //                     s.learner.unexecuted_learner_state[opn].candidate_learned_value)
    //             && s' == s.(executor := s'.executor)
    //             && sent_packets == []
    //     else
    //         s' == s && sent_packets == []
    // }

    // predicate LReplicaNextSpontaneousMaybeMakeDecision(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    // {
    //     var opn := s.executor.ops_complete;
    //     var quorum := LMinQuorumSize(s.acceptor.constants.all.config);
    //     if  && s.executor.next_op_to_execute.OutstandingOpUnknown?
    //         && opn in s.learner.unexecuted_learner_state
    //         && LearnerStateCorrect(s.learner.unexecuted_learner_state, s.learner.max_ballot_seen, s.constants.all.config)
    //         && |s.learner.unexecuted_learner_state[opn].received_2bs| >= quorum
    //         // && IsWeakQuorumSendSame2b(s.learner.unexecuted_learner_state[opn].candidate_learned_value, quorum)
    //         && HasReceivedSame2bFromWeakQuorum(s.learner.unexecuted_learner_state[opn], quorum)
    //     then
    //         if exists p :: 
    //                 && p in s.learner.unexecuted_learner_state[opn].received_2bs
    //                 && CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, p.msg.val_2b) >= quorum
    //         then
    //             var p :| p in s.learner.unexecuted_learner_state[opn].received_2bs
    //                 && CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, p.msg.val_2b) >= quorum;
    //             && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn, p.msg.val_2b)
    //         // exists v ::
    //         //     v in s.learner.unexecuted_learner_state[opn].candidate_learned_value
    //         //     && CountMatchesInSeq(s.learner.unexecuted_learner_state[opn].candidate_learned_value, x => x == v) >= quorum
    //         //     && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn, v)
    //         // && LExecutorGetDecision(s.executor, s'.executor, s.learner.max_ballot_seen, opn,
    //         //                     s.learner.unexecuted_learner_state[opn].candidate_learned_value)
    //             && s' == s.(executor := s'.executor)
    //             && sent_packets == []
    //         else
    //             s' == s && sent_packets == []
    //     else
    //         s' == s && sent_packets == []
    // }

    predicate LReplicaNextSpontaneousMaybeExecute(s:LReplica, s':LReplica, sent_packets:seq<RslPacket>)
    {
        if  && s.executor.next_op_to_execute.OutstandingOpKnown?
            && LtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val)
            && LReplicaConstantsValid(s.executor.constants) then
            var v := s.executor.next_op_to_execute.v;
            && LProposerResetViewTimerDueToExecution(s.proposer, s'.proposer, v)
            && LLearnerForgetDecision(s.learner, s'.learner, s.executor.ops_complete)
            && LAcceptorForgetReceived2avs(s.acceptor, s'.acceptor, s.executor.ops_complete)
            && LExecutorExecute(s.executor, s'.executor, sent_packets)
            && s' == s.(acceptor := s'.acceptor, 
                        proposer := s'.proposer, 
                        learner := s'.learner, 
                        executor := s'.executor)
        else
            s' == s && sent_packets == []
    }

    predicate LReplicaNextReadClockMaybeSendHeartbeat(s:LReplica, s':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
    {
        if clock.t < s.nextHeartbeatTime then
            s' == s && sent_packets == []
        else
            && s'.nextHeartbeatTime == UpperBoundedAddition(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val)
            && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                RslMessage_Heartbeat(s.proposer.election_state.current_view,
                                                        s.constants.my_index in s.proposer.election_state.current_view_suspectors,
                                                        s.executor.ops_complete),
                                sent_packets)
            && s' == s.(nextHeartbeatTime := s'.nextHeartbeatTime)
    }

    predicate LReplicaNextReadClockCheckForViewTimeout(s:LReplica, s':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
    {
        && LProposerCheckForViewTimeout(s.proposer, s'.proposer, clock.t)
        && sent_packets == []
        && s' == s.(proposer := s'.proposer)
    }

    predicate LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s:LReplica, s':LReplica, clock:ClockReading, sent_packets:seq<RslPacket>)
    {
        && LProposerCheckForQuorumOfViewSuspicions(s.proposer, s'.proposer, clock.t)
        && sent_packets == []
        && s' == s.(proposer := s'.proposer)
    }

    // function {:opaque} ExtractSentPacketsFromIos(ios:seq<RslIo>) : seq<RslPacket>
    //     ensures forall p :: p in ExtractSentPacketsFromIos(ios) <==> LIoOpSend(p) in ios
    // {
    //     if |ios| == 0 then
    //         []
    //     else if ios[0].LIoOpSend? then
    //         [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
    //     else
    //         ExtractSentPacketsFromIos(ios[1..])
    // }

    // predicate LReplicaNextReadClockAndProcessPacket(s:LReplica, s':LReplica, ios:seq<RslIo>)
    //     requires |ios| >= 1
    //     requires ios[0].LIoOpReceive?
    //     requires ios[0].r.msg.RslMessage_Heartbeat?
    // {
    //     && |ios| > 1
    //     && ios[1].LIoOpReadClock?
    //     && (forall io :: io in ios[2..] ==> io.LIoOpSend?)
    //     && LReplicaNextProcessHeartbeat(s, s', ios[0].r, ios[1].t, ExtractSentPacketsFromIos(ios))
    // }

    // predicate LReplicaNextProcessPacketWithoutReadingClock(s:LReplica, s':LReplica, ios:seq<RslIo>)
    //     requires |ios| >= 1
    //     requires ios[0].LIoOpReceive?
    //     requires !ios[0].r.msg.RslMessage_Heartbeat?
    // {
    //     && (forall io :: io in ios[1..] ==> io.LIoOpSend?)
    //     && var sent_packets := ExtractSentPacketsFromIos(ios);
    //         match ios[0].r.msg
    //         case RslMessage_Invalid => LReplicaNextProcessInvalid(s, s', ios[0].r, sent_packets)
    //         case RslMessage_Request(_, _) => LReplicaNextProcessRequest(s, s', ios[0].r, sent_packets)
    //         case RslMessage_1a(_) => LReplicaNextProcess1a(s, s', ios[0].r, sent_packets)
    //         case RslMessage_1b(_, _, _/*, _*/) => LReplicaNextProcess1b(s, s', ios[0].r, sent_packets)
    //         case RslMessage_StartingPhase2(_, _) => LReplicaNextProcessStartingPhase2(s, s', ios[0].r, sent_packets)
    //         case RslMessage_1c(_, _, _/*, _*/) => LReplicaNextProcess1c(s, s', ios[0].r, sent_packets)
    //         case RslMessage_2av(_, _, _) => LReplicaNextProcess2av(s, s', ios[0].r, sent_packets)
    //         case RslMessage_2b(_, _, _) => LReplicaNextProcess2b(s, s', ios[0].r, sent_packets)
    //         case RslMessage_Reply(_, _) => LReplicaNextProcessReply(s, s', ios[0].r, sent_packets)
    //         case RslMessage_AppStateRequest(_, _) => LReplicaNextProcessAppStateRequest(s, s', ios[0].r, sent_packets)
    //         case RslMessage_AppStateSupply(_, _, _, _) => LReplicaNextProcessAppStateSupply(s, s', ios[0].r, sent_packets)
    // }

    // predicate LReplicaNextProcessPacket(s:LReplica, s':LReplica, ios:seq<RslIo>)
    // {
    //     && |ios| >= 1
    //     && if ios[0].LIoOpTimeoutReceive? then
    //         s' == s && |ios| == 1
    //         else
    //         (&& ios[0].LIoOpReceive?
    //         && if ios[0].r.msg.RslMessage_Heartbeat? then
    //             LReplicaNextReadClockAndProcessPacket(s, s', ios)
    //             else
    //             LReplicaNextProcessPacketWithoutReadingClock(s, s', ios)
    //         )
    // }

    // function LReplicaNumActions() : int
    // {
    //     12
    // }

    // predicate SpontaneousIos(ios:seq<RslIo>, clocks:int)
    //     requires 0<=clocks<=1
    // {
    //     && clocks <= |ios|
    //     && (forall i :: 0<=i<clocks ==> ios[i].LIoOpReadClock?)
    //     && (forall i :: clocks<=i<|ios| ==> ios[i].LIoOpSend?)
    // }

    // function SpontaneousClock(ios:seq<RslIo>) : ClockReading
    // {
    //     if SpontaneousIos(ios, 1) then ClockReading(ios[0].t) else ClockReading(0) // nonsense to avoid putting a precondition on this function
    // }

    // predicate LReplicaNoReceiveNext(s:LReplica, nextActionIndex:int, s':LReplica, ios:seq<RslIo>)
    // {
    //     var sent_packets := ExtractSentPacketsFromIos(ios);

    //     if nextActionIndex == 1 then
    //         && SpontaneousIos(ios, 0)
    //         && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s', sent_packets)
    //     else if nextActionIndex == 2 then
    //         && SpontaneousIos(ios, 0)
    //         && LReplicaNextSpontaneousMaybeEnterPhase2(s, s', sent_packets)
    //     else if nextActionIndex == 3 then
    //         && SpontaneousIos(ios, 1)
    //         && LReplicaNextReadClockMaybeNominateValueAndSend1c(s, s', SpontaneousClock(ios), sent_packets)
    //     else if nextActionIndex == 4 then
    //         && SpontaneousIos(ios, 0)
    //         && LReplicaNextSpontaneousMaybeDecide2bVal(s, s', sent_packets)
    //     else if nextActionIndex == 5 then
    //         && SpontaneousIos(ios, 0)
    //         && LReplicaNextSpontaneousMaybeSend2b(s, s', sent_packets)
    //     else if nextActionIndex == 6 then
    //         && SpontaneousIos(ios, 0)
    //         && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sent_packets)
    //     else if nextActionIndex == 7 then
    //         && SpontaneousIos(ios, 0)
    //         && LReplicaNextSpontaneousMaybeMakeDecision(s, s', sent_packets)
    //     else if nextActionIndex == 8 then
    //         && SpontaneousIos(ios, 0)
    //         && LReplicaNextSpontaneousMaybeExecute(s, s', sent_packets)
    //     else if nextActionIndex == 9 then
    //         && SpontaneousIos(ios, 1)
    //         && LReplicaNextReadClockCheckForViewTimeout(s, s', SpontaneousClock(ios), sent_packets)
    //     else if nextActionIndex == 10 then
    //         && SpontaneousIos(ios, 1)
    //         && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', SpontaneousClock(ios), sent_packets)
    //     else
    //         && nextActionIndex == 11
    //         && SpontaneousIos(ios, 1)
    //         && LReplicaNextReadClockMaybeSendHeartbeat(s, s', SpontaneousClock(ios), sent_packets)
    // }

    // // predicate LReplicaNoReceiveNext(s:LReplica, nextActionIndex:int, s':LReplica, ios:seq<RslIo>)
    // // {
    // //     var sent_packets := ExtractSentPacketsFromIos(ios);

    // //     if nextActionIndex == 1 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s', sent_packets)
    // //     else if nextActionIndex == 2 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousMaybeEnterPhase2(s, s', sent_packets)
    // //     else if nextActionIndex == 3 then
    // //         && SpontaneousIos(ios, 1)
    // //         && LReplicaNextReadClockMaybeNominateValueAndSend1c(s, s', SpontaneousClock(ios), sent_packets)
    // //     else if nextActionIndex == 4 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sent_packets)
    // //     else if nextActionIndex == 5 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousMaybeMakeDecision(s, s', sent_packets)
    // //     else if nextActionIndex == 6 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousMaybeExecute(s, s', sent_packets)
    // //     else if nextActionIndex == 7 then
    // //         && SpontaneousIos(ios, 1)
    // //         && LReplicaNextReadClockCheckForViewTimeout(s, s', SpontaneousClock(ios), sent_packets)
    // //     else if nextActionIndex == 8 then
    // //         && SpontaneousIos(ios, 1)
    // //         && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', SpontaneousClock(ios), sent_packets)
    // //     else
    // //         && nextActionIndex == 9
    // //         && SpontaneousIos(ios, 1)
    // //         && LReplicaNextReadClockMaybeSendHeartbeat(s, s', SpontaneousClock(ios), sent_packets)
    // // }

    // // predicate LReplicaNoReceiveNext(s:LReplica, nextActionIndex:int, s':LReplica, ios:seq<RslIo>)
    // // {
    // //     var sent_packets := ExtractSentPacketsFromIos(ios);

    // //     if nextActionIndex == 1 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s', sent_packets)
    // //     else if nextActionIndex == 2 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousMaybeEnterPhase2(s, s', sent_packets)
    // //     else if nextActionIndex == 3 then
    // //         && SpontaneousIos(ios, 1)
    // //         && LReplicaNextReadClockMaybeNominateValueAndSend1c(s, s', SpontaneousClock(ios), sent_packets)
    // //     else if nextActionIndex == 4 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sent_packets)
    // //     else if nextActionIndex == 5 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousMaybeMakeDecision(s, s', sent_packets)
    // //     else if nextActionIndex == 6 then
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousMaybeExecute(s, s', sent_packets)
    // //     else if nextActionIndex == 7 then
    // //         && SpontaneousIos(ios, 1)
    // //         && LReplicaNextReadClockCheckForViewTimeout(s, s', SpontaneousClock(ios), sent_packets)
    // //     else if nextActionIndex == 8 then
    // //         && SpontaneousIos(ios, 1)
    // //         && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s', SpontaneousClock(ios), sent_packets)
    // //     else if nextActionIndex == 9 then
    // //         && SpontaneousIos(ios, 1)
    // //         && LReplicaNextReadClockMaybeSendHeartbeat(s, s', SpontaneousClock(ios), sent_packets)
    // //     else
    // //         && nextActionIndex == 10
    // //         && SpontaneousIos(ios, 0)
    // //         && LReplicaNextSpontaneousMaybeMakeSend2b(s, s', sent_packets)
    // // }

    // datatype LScheduler = LScheduler(replica:LReplica, nextActionIndex:int)

    // predicate LSchedulerInit(s:LScheduler, c:LReplicaConstants)
    //     requires WellFormedLConfiguration(c.all.config)
    // {
    //     && LReplicaInit(s.replica, c)
    //     && s.nextActionIndex == 0
    // }

    // predicate LSchedulerNext(s:LScheduler, s':LScheduler, ios:seq<RslIo>)
    // {
    //     && s'.nextActionIndex == (s.nextActionIndex + 1) % LReplicaNumActions()
    //     && if s.nextActionIndex == 0 then
    //         LReplicaNextProcessPacket(s.replica, s'.replica, ios)
    //         else
    //         LReplicaNoReceiveNext(s.replica, s.nextActionIndex, s'.replica, ios)
    // }

}