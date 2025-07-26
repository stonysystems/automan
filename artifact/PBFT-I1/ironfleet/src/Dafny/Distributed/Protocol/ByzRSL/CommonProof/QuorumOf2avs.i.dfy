include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"

module CommonProof__QuorumOf2avs_i {
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Executor_i
import opened LiveByzRSL__Message_i
import opened LiveByzRSL__Proposer_i
import opened LiveByzRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened Concrete_NodeIdentity_i
import opened Temporal__Temporal_s
import opened Collections__Sets_i
import opened Environment_s

datatype QuorumOf2avs = QuorumOf2avs(
    c:LConstants,
    indices:set<int>,
    packets:seq<RslPacket>,
    bal:Ballot,
    opn:OperationNumber,
    v:RequestBatch
)

predicate IsValidQuorumOf2avs(
    ps:RslState,
    q:QuorumOf2avs
)
{
    && |q.indices| >= LByzQuorumSize(ps.constants.config)
    && |q.packets| == |ps.constants.config.replica_ids|
    && (forall idx :: idx in q.indices ==> && 0 <= idx < |ps.constants.config.replica_ids|
                                    && var p := q.packets[idx];
                                    && p.src == ps.constants.config.replica_ids[idx]
                                    && p.msg.RslMessage_2av?
                                    && p.msg.opn_2av == q.opn
                                    && p.msg.val_2av == q.v
                                    && p.msg.bal_2av == q.bal
                                    && p in ps.environment.sentPackets)
}

predicate IsValidQuorumOf2avsSequence(ps:RslState, qs:seq<QuorumOf2avs>)
{
  forall opn :: 0 <= opn < |qs| ==> qs[opn].opn == opn && IsValidQuorumOf2avs(ps, qs[opn])
}

lemma lemma_QuorumOf2avsStaysValid(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    j:int,
    q:QuorumOf2avs
)
    requires IsValidBehaviorPrefix(b, c, j)
    requires IsValidQuorumOf2avs(b[i], q)
    requires 0 <= i <= j
    ensures IsValidQuorumOf2avs(b[j], q)
{
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, j);

    forall idx | idx in q.indices
        ensures q.packets[idx] in b[j].environment.sentPackets
    {
        lemma_PacketStaysInSentPackets(b, c, i, j, q.packets[idx]);
    }
}

// lemma lemma_ChosenQuorum2avsMatchValue(
//     b:Behavior<RslState>,
//     c:LConstants,
//     i:int,
//     q1:QuorumOf2avs,
//     q2:QuorumOf2avs
// )
//     requires IsValidBehaviorPrefix(b, c, i)
//     requires 0 <= i
//     requires IsValidQuorumOf2avs(b[i], q1)
//     requires IsValidQuorumOf2avs(b[i], q2)
//     requires q1.opn == q2.opn
//     ensures  q1.v == q2.v
// {
//     lemma_ConstantsAllConsistent(b, c, i);

//     var idx1 :| idx1 in q1.indices;
//     var idx2 :| idx2 in q2.indices;
//     var p1_2b := q1.packets[idx1];
//     var p2_2b := q2.packets[idx2];
// }
}