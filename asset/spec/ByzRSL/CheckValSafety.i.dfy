include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Constants.i.dfy"
include "Broadcast.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"

module LiveByzRSL__CheckValSafety_i {
import opened LiveByzRSL__Types_i
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__Broadcast_i
import opened LiveByzRSL__Message_i
import opened Concrete_NodeIdentity_i
import opened Common__UpperBound_s
import opened Collections__CountMatches_i

// datatype Received1b = Received(p:RslPacket) | UnReceived()

// datatype ProposerTuple = ProposerTuple(received_1b_message_sender:set<NodeIdentity>, msg1bs:seq<RslMessage>)

// datatype ProposerTuple = ProposerTuple(indices:set<int>, packets:seq<Received1b>)

// predicate LSetOfMessage1b(tup:ProposerTuple)
// {
//     forall m :: m in tup.msg1bs ==> m.RslMessage_1b?
// }

function {:opaque} Convert1bPacketsSeqToMsgSeq(S:seq<RslPacket>) : seq<RslMessage>
    requires LSeqOfMessage1b(S)
    requires forall p :: p in S ==> p.msg.RslMessage_1b?
    ensures |S| == |Convert1bPacketsSeqToMsgSeq(S)|
    ensures forall m :: m in Convert1bPacketsSeqToMsgSeq(S) ==> m.RslMessage_1b?
    // ensures forall i :: 0 <= i < |S| ==> Convert1bPacketsSeqToMsgSeq(S)[i] == S[i].msg
{
    if |S| == 0 then
        []
    else 
        [S[0].msg] + Convert1bPacketsSeqToMsgSeq(S[1..])
}

predicate LSeqOfMessage1b(S:seq<RslPacket>)
{
    forall p :: p in S ==> p.msg.RslMessage_1b?
}

predicate LSetOfMessage1bAboutBallot(S:seq<RslPacket>, b:Ballot)
{
    && LSeqOfMessage1b(S)
    && (forall p :: p in S ==> p.msg.bal_1b == b)
}

predicate LAllAcceptorsHadNoProposal(S:seq<RslPacket>, opn:OperationNumber)
    requires LSeqOfMessage1b(S)
{
    forall p :: p in S ==> !(opn in p.msg.votes)
}

// function CountLtThanBalInSent2bs(v:RequestBatch, c:Ballot, opn:OperationNumber, S:seq<RslMessage>) : int
//     requires forall m :: m in S ==> m.RslMessage_1b?
// {
//     if |S| == 0 then
//         0
//     else
//         CountLtThanBalInSent2bs(v, c, opn, S[1..]) + if opn in S[0].sent2bs && BalLt(S[0].sent2bs[opn].max_vbal, c) then 1 else 0 
// }

// function CountLqThanBalInSent2bs(v:RequestBatch, c:Ballot, opn:OperationNumber, S:seq<RslMessage>) : int
//     requires forall m :: m in S ==> m.RslMessage_1b?
// {
//     if |S| == 0 then
//         0
//     else
//         CountLqThanBalInSent2bs(v, c, opn, S[1..]) + if opn in S[0].sent2bs && BalLeq(S[0].sent2bs[opn].max_vbal, c) then 1 else 0 
// }

function CountInVotes(v:RequestBatch, c:Ballot, opn:OperationNumber, S:seq<RslPacket>) : int
    requires forall p :: p in S ==> p.msg.RslMessage_1b?
    ensures CountInVotes(v, c, opn, S) > 0 ==> exists p :: p in S && opn in p.msg.votes && BalLeq(c, p.msg.votes[opn].max_value_bal) 
{
    if |S| == 0 then
        0
    else
        CountInVotes(v, c, opn, S[1..]) + if opn in S[0].msg.votes 
                                            && BalLeq(c, S[0].msg.votes[opn].max_value_bal) 
                                            && S[0].msg.votes[opn].max_val == v 
                                            then 1 else 0 
}

predicate LSetOfMessage1b(S:seq<RslPacket>)
{
    forall p :: p in S ==> p.msg.RslMessage_1b?
}

predicate Lmax_balInS(c:Ballot, S:seq<RslPacket>, opn:OperationNumber)
    requires LSetOfMessage1b(S)
{
    forall p :: p in S && opn in p.msg.votes ==> BalLeq(p.msg.votes[opn].max_value_bal, c)
}

predicate LExistsBallotInS(v:RequestBatch, c:Ballot, S:seq<RslPacket>, opn:OperationNumber)
    requires LSetOfMessage1b(S)
{
    exists p :: && p in S
                && opn in p.msg.votes
                && p.msg.votes[opn].max_value_bal==c
                && p.msg.votes[opn].max_val==v
}

predicate LValIsHighestNumberedProposalAtBallot(v:RequestBatch, c:Ballot, S:seq<RslPacket>, opn:OperationNumber)
    requires LSetOfMessage1b(S)
{
    && Lmax_balInS(c, S, opn)
    && LExistsBallotInS(v, c, S, opn)
}

predicate AllVotesWithLargerBalHasSameValue(v:RequestBatch, b:Ballot, p1bs:seq<RslPacket>, opn:OperationNumber)
    requires forall p :: p in p1bs ==> p.msg.RslMessage_1b?
{
    forall p :: p in p1bs && opn in p.msg.votes && BalLeq(b, p.msg.votes[opn].max_value_bal) ==> p.msg.votes[opn].max_val == v
}

predicate LValIsSafeAt(v:RequestBatch, /*b:Ballot,*/ p1bs:seq<RslPacket>, opn:OperationNumber, byzq:int, wq:int)
    requires forall p :: p in p1bs ==> p.msg.RslMessage_1b?
    // ensures LValIsSafeAt(v, msg1bs, opn, byzq, wq) ==> 
    //     (exists p :: p in msg1bs && opn in p.votes && LValIsHighestNumberedProposalAtBallot(v, p.votes[opn].max_value_bal, msg1bs, opn))
{
    // exists p :: 
    //         && p in msg1bs
    //         && opn in p.votes
    //         && CountInVotes(v, c, opn, msg1bs) >= wq
    exists c :: 
                && CountInVotes(v, c, opn, p1bs) >= wq
                && AllVotesWithLargerBalHasSameValue(v, c, p1bs, opn)
                // && !(exists q :: q in msg1bs && opn in q.votes && q.votes[opn].max_value_bal > c && q.votes[opn].max_val != v)
}

    // predicate LCountMatch(v:RequestBatch, c:Ballot, S:set<RslMessage>, opn:OperationNumber)
//     requires forall s :: s in S ==> s.RslMessage_1b?
// {
//     CountMatchesInSet(S, x => x.sent2bs[opn].max_vbal <= c)
// }

// predicate LValIsSafeAt(v:RequestBatch, /*b:Ballot,*/ msg1bs:seq<RslMessage>, opn:OperationNumber, byzq:int, wq:int)
//     requires forall m :: m in msg1bs ==> m.RslMessage_1b?
// {
//     exists c :: 
//                 // 是否需要这个bal判断呢？TLA+里有
//                 // && BalLt(c, b) 
//                 && CountLtThanBalInSent2bs(v, c, opn, msg1bs) < byzq
//                 && CountLqThanBalInSent2bs(v, c, opn, msg1bs) >= byzq
//                 && (forall m :: m in msg1bs && opn in m.sent2bs ==> m.sent2bs[opn].max_vval == v)
//                 && CountInVotes(v, c, opn, msg1bs) >= wq
// }

}