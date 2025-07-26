include "Environment.i.dfy"
include "Configuration.i.dfy"
include "Constants.i.dfy"
include "Broadcast.i.dfy"
include "CheckValSafety.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"
include "../../Common/Collections/Maps.i.dfy"


module LiveByzRSL__Acceptor_i {
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__Broadcast_i
import opened LiveByzRSL__Types_i
import opened LiveByzRSL__Message_i
import opened LiveByzRSL__CheckValSafety_i
import opened Collections__CountMatches_i
import opened Environment_s
import opened Common__UpperBound_s
import opened Collections__Maps_i
import opened Concrete_NodeIdentity_i

datatype AcceptorTuple = AcceptorTuple(received_2av_packets:seq<RslPacket>)
type Received2avs = map<OperationNumber, AcceptorTuple>

datatype ValToBeSent2b = ValToBeSent2bKnown(v:RequestBatch, bal:Ballot) | ValToBeSent2bUnknown()

datatype LAcceptor = LAcceptor(
    constants:LReplicaConstants,
    max_bal:Ballot,
    votes:Votes,
    last_checkpointed_operation:seq<OperationNumber>,
    log_truncation_point:OperationNumber,
    received_1b_packets:seq<RslPacket>,
    // sent_2bs:Sent2bs,
    received_2avs:Received2avs,
    opn_to_be_send_2b:OperationNumber,
    val_to_be_sent_2b:ValToBeSent2b
)

function CountMatchedValInReceived2avs(s:seq<RslPacket>, v:RequestBatch) : int
    requires forall p :: p in s ==> p.msg.RslMessage_2av?
{
    if |s| == 0 then
        0
    else
        CountMatchedValInReceived2avs(s[..|s|-1], v) + if s[|s|-1].msg.val_2av == v then 1 else 0
}

function CountMatchedInRequestBatches(s:seq<RequestBatch>, v:RequestBatch) : int
{
    if |s| == 0 then
        0
    else
        CountMatchedInRequestBatches(s[..|s|-1], v) + if s[|s|-1] == v then 1 else 0
}

predicate HasReceivedSame2avFromByzQuorum(r2avs:AcceptorTuple, n:int)
    requires forall p :: p in r2avs.received_2av_packets ==> p.msg.RslMessage_2av?
{
    exists p :: p in r2avs.received_2av_packets && CountMatchedValInReceived2avs(r2avs.received_2av_packets, p.msg.val_2av) >= n
}

predicate IsByzQuorumSendSame2av(vals:seq<RequestBatch>, n:int)
{
    exists v :: v in vals && CountMatchedInRequestBatches(vals, v) >= n
}

predicate HasReceived2avOfOpn(received_2avs:Received2avs, opn:OperationNumber)
{
    opn in received_2avs
}


predicate AcceptorTupleIsUniqueSeq(tup:AcceptorTuple)
{
  && (forall i,j :: 0 <= i < |tup.received_2av_packets| && 0 <= j < |tup.received_2av_packets| && i != j 
                  ==> tup.received_2av_packets[i] != tup.received_2av_packets[j] && tup.received_2av_packets[i].src != tup.received_2av_packets[j].src)
}

predicate Received2avSetCorrect(r2avs:AcceptorTuple, bal:Ballot, opn:OperationNumber, c:LConfiguration)
{
    && |r2avs.received_2av_packets| <= |c.replica_ids|
    && (forall p :: p in r2avs.received_2av_packets ==> 
                && p.msg.RslMessage_2av?
                && p.msg.opn_2av == opn
                && p.msg.bal_2av == bal
                && p.src in c.replica_ids)
}

predicate AcceptorStateCorrect(r2avs:Received2avs, bal:Ballot, c:LConfiguration)
{
    (forall opn :: opn in r2avs ==> 
        && Received2avSetCorrect(r2avs[opn], bal, opn, c)
        && AcceptorTupleIsUniqueSeq(r2avs[opn]))
}


predicate IsLogTruncationPointValid(log_truncation_point:OperationNumber, last_checkpointed_operation:seq<OperationNumber>,
                                    config:LConfiguration)
{
    IsNthHighestValueInSequence(log_truncation_point,
                                last_checkpointed_operation,
                                LByzQuorumSize(config))
}

predicate RemoveVotesBeforeLogTruncationPoint(votes:Votes, votes':Votes, log_truncation_point:OperationNumber)
{
    // && (forall opn :: opn in votes' ==> opn in votes && votes'[opn] == votes[opn])
    // && (forall opn :: opn < log_truncation_point ==> opn !in votes')
    // && (forall opn :: opn >= log_truncation_point && opn in votes ==> opn in votes')
    // && (forall opn :: opn in votes && opn >= log_truncation_point ==> opn in votes' && votes'[opn] == votes[opn])
    && (forall opn :: opn in votes' <==> opn in votes && opn >= log_truncation_point)
    && (forall opn :: opn in votes' ==> votes'[opn] == votes[opn])
}

// predicate RemoveSent2bsBeforeLogTruncationPoint(sent2bs:Sent2bs, sent2bs':Sent2bs, log_truncation_point:OperationNumber)
// {
//     && (forall opn :: opn in sent2bs' ==> opn in sent2bs && sent2bs'[opn] == sent2bs[opn])
//     && (forall opn :: opn < log_truncation_point ==> opn !in sent2bs')
//     && (forall opn :: opn >= log_truncation_point && opn in sent2bs ==> opn in sent2bs')
//     && (forall opn :: opn in sent2bs && opn >= log_truncation_point ==> opn in sent2bs' && sent2bs'[opn] == sent2bs[opn])
// }

predicate LAddVoteAndRemoveOldOnes(votes:Votes, votes':Votes, new_opn:OperationNumber, new_vote:Vote, log_truncation_point:OperationNumber)
{
    /*
    && (forall opn :: opn in votes' <==> opn >= log_truncation_point && (opn in votes || opn == new_opn))
    && (forall opn :: opn in votes' ==> votes'[opn] == (if opn == new_opn then new_vote else votes[opn]))
    */

    // && (forall opn :: opn in votes' <==> opn >= log_truncation_point && (opn in votes || opn == new_opn))
    // && (forall opn :: opn in votes' ==> votes'[opn] == (if opn == new_opn then new_vote else votes[opn]))
    // && (forall opn :: opn in (votes.Keys + {new_opn}) && opn >= log_truncation_point ==> opn in votes' && votes'[opn] == (if opn == new_opn then new_vote else votes[opn]))
    && (forall opn :: opn in votes' <==> opn in (votes.Keys + {new_opn}) && opn >= log_truncation_point)
    && (forall opn :: opn in votes' ==> votes'[opn] == (if opn == new_opn then new_vote else votes[opn]))
}


predicate LAcceptorInit(a:LAcceptor, c:LReplicaConstants)
{
    && a.constants == c
    && a.max_bal == Ballot(0,0)
    && a.votes == map []
    && |a.last_checkpointed_operation| == |c.all.config.replica_ids|
    && (forall idx {:trigger a.last_checkpointed_operation[idx]} :: 0 <= idx < |a.last_checkpointed_operation| ==>
                                                                    a.last_checkpointed_operation[idx] == 0)
    && a.log_truncation_point == 0
    && a.received_2avs == map[]
    && a.received_1b_packets == []
    && a.opn_to_be_send_2b == 0
    && a.val_to_be_sent_2b == ValToBeSent2bUnknown()
}

predicate LAcceptorMaybeEnterNewView(s:LAcceptor, s':LAcceptor)
{
    s' == s.(received_1b_packets := [])
}

predicate LAcceptorProcess1a(s:LAcceptor, s':LAcceptor, inp:RslPacket, sent_packets:seq<RslPacket>)
    requires inp.msg.RslMessage_1a?
{
    var m := inp.msg;
    if inp.src in s.constants.all.config.replica_ids && BalLt(s.max_bal, m.bal_1a) && LReplicaConstantsValid(s.constants) then
        && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, RslMessage_1b(m.bal_1a, s.log_truncation_point, s.votes/*, s.sent_2bs*/), sent_packets)
        && s' == s.(max_bal := m.bal_1a)
    else
        s' == s && sent_packets == []
}

predicate LAcceptorProcess1b(s:LAcceptor, s':LAcceptor, p:RslPacket)
    requires p.msg.RslMessage_1b?
    requires p.src in s.constants.all.config.replica_ids
    requires forall other_packet :: other_packet in s.received_1b_packets ==> other_packet.src != p.src
{
    s' == s.(received_1b_packets := s.received_1b_packets + [p])
}

predicate LAcceptorProcess1c(s:LAcceptor, s':LAcceptor, inp:RslPacket, sent_packets:seq<RslPacket>)
    requires inp.msg.RslMessage_1c?
    requires inp.src in s.constants.all.config.replica_ids
    requires BalLeq(s.max_bal, inp.msg.bal_1c)
    requires LeqUpperBound(inp.msg.opn_1c, s.constants.all.params.max_integer_val)
{ 
    var m := inp.msg;

    var newLogTruncationPoint := if inp.msg.opn_1c - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then
                                    inp.msg.opn_1c - s.constants.all.params.max_log_length + 1
                                else
                                    s.log_truncation_point;
    && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, RslMessage_2av(m.bal_1c, m.opn_1c, m.val_1c), sent_packets)
    && (if s.log_truncation_point <= inp.msg.opn_1c then
        && LAddVoteAndRemoveOldOnes(s.votes, s'.votes, m.opn_1c, Vote(m.bal_1c, m.val_1c), newLogTruncationPoint)
    else
        s'.votes == s.votes
        )
    && s' == s.(max_bal := m.bal_1c, log_truncation_point := newLogTruncationPoint, votes := s'.votes)
}


predicate LAcceptorProcess2av(s:LAcceptor, s':LAcceptor, inp:RslPacket)
    requires inp.msg.RslMessage_2av?
{
    var m := inp.msg;
    var opn := m.opn_2av;
    if inp.src !in s.constants.all.config.replica_ids || BalLt(m.bal_2av, s.max_bal) then
        s' == s
    else if BalLt(s.max_bal, m.bal_2av) then
        var tup' := AcceptorTuple([inp]);
        s' == s.(max_bal := m.bal_2av,
                received_2avs := map[opn := tup'])
    else if opn !in s.received_2avs then
        var tup' := AcceptorTuple([inp]);
        s' == s.(received_2avs := s.received_2avs[opn := tup'])
    else if (exists p :: p in s.received_2avs[opn].received_2av_packets && p.src == inp.src) then
        s' == s 
    else
        var tup := s.received_2avs[opn];
        var tup' := tup.(received_2av_packets := tup.received_2av_packets + [inp]);
        s' == s.(received_2avs := s.received_2avs[opn := tup'])
    // else
    //     s' == s
}


predicate LAcceptorDecide2bVal(s:LAcceptor, s':LAcceptor, bal:Ballot, opn:OperationNumber, v:RequestBatch)
    requires s.opn_to_be_send_2b in s.received_2avs
    requires opn == s.opn_to_be_send_2b
    // requires |s.received_2avs[s.opn_to_be_send_2b].received_2av_message_senders| >= LByzQuorumSize(s.constants.all.config)
    // requires IsByzQuorumSendSame2av(s.received_2avs[s.opn_to_be_send_2b].candidate_value, LByzQuorumSize(s.constants.all.config)) 
    // requires Received2avsAreValid(s, s.opn_to_be_send_2b)
    requires s.val_to_be_sent_2b.ValToBeSent2bUnknown?
    // ensures s'.val_to_be_sent_2b.ValToBeSent2bKnown?
{
    && s' == s.(val_to_be_sent_2b := ValToBeSent2bKnown(v, bal))
}


predicate LAcceptorSent2b(s:LAcceptor, s':LAcceptor, sent_packets:seq<RslPacket>)
    requires s.val_to_be_sent_2b.ValToBeSent2bKnown?
    requires s.val_to_be_sent_2b.bal == s.max_bal
    // requires s.opn_to_be_send_2b in s.received_2avs
    // requires |s.received_2avs[s.opn_to_be_send_2b].received_2av_message_senders| >= LByzQuorumSize(s.constants.all.config)
    // requires IsByzQuorumSendSame2av(s.received_2avs[s.opn_to_be_send_2b].candidate_value, LByzQuorumSize(s.constants.all.config)) 
    // requires Received2avsAreValid(s, s.opn_to_be_send_2b)
{
    var opn := s.opn_to_be_send_2b;
    var v := s.val_to_be_sent_2b.v;
    var bal := s.val_to_be_sent_2b.bal;
    var newLogTruncationPoint := if opn - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then
                                        opn - s.constants.all.params.max_log_length + 1
                                    // else if opn < s.log_truncation_point then
                                    //     opn
                                    else
                                        s.log_truncation_point;
    && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, RslMessage_2b(bal, opn, v), sent_packets)
    && (if s'.log_truncation_point <= opn /*&& opn !in s.votes*/ then
            && LAddVoteAndRemoveOldOnes(s.votes, s'.votes, opn, Vote(bal, v), newLogTruncationPoint)
            && s'.log_truncation_point == newLogTruncationPoint
        else
            && s'.votes == s.votes
            && s'.log_truncation_point == s.log_truncation_point
            )
    && s' == s.(
                // sent_2bs := s.sent_2bs[opn := Sent2b(s.max_bal, v)],
                opn_to_be_send_2b := s.opn_to_be_send_2b + 1,
                val_to_be_sent_2b := ValToBeSent2bUnknown(),
                votes := s'.votes,
                log_truncation_point := s'.log_truncation_point)
}


predicate LAcceptorForgetReceived2avs(s:LAcceptor, s':LAcceptor, opn:OperationNumber)
{
    if opn in s.received_2avs then
        s' == s.(received_2avs := RemoveElt(s.received_2avs, opn))
    else
        s' == s
}

predicate LAcceptorProcessHeartbeat(s:LAcceptor, s':LAcceptor, inp:RslPacket)
    requires inp.msg.RslMessage_Heartbeat?
{
    if inp.src in s.constants.all.config.replica_ids then
        var sender_index := GetReplicaIndex(inp.src, s.constants.all.config);
        if 0 <= sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then
            s' == s.(last_checkpointed_operation := s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt])
        else
            s' == s
    else
    s' == s
}

predicate LAcceptorTruncateLog(s:LAcceptor, s':LAcceptor, opn:OperationNumber)
{
    if opn <= s.log_truncation_point then
        s' == s
    else
        && RemoveVotesBeforeLogTruncationPoint(s.votes, s'.votes, opn)
        && s' == s.(log_truncation_point := opn, votes := s'.votes)
}
}