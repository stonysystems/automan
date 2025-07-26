include "Types.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"

module LiveByzRSL__Configuration_i {
import opened LiveByzRSL__Types_i
import opened Collections__Sets_i
import opened Collections__Seqs_i
import opened Concrete_NodeIdentity_i

// 1

datatype LConfiguration = LConfiguration(
  clientIds:set<NodeIdentity>,
  replica_ids:seq<NodeIdentity>
  )

// function LByzNodeAllowed(c:LConfiguration):int
// {
//     |c.replica_ids| / 3
// }
// // Jay suggests using a less-general notion of quorum.
// function LMinQuorumSize(c:LConfiguration) : int
// {
//     LByzNodeAllowed(c) + 1
// }

// function LByzQuorumSize(c:LConfiguration) : int
// {
//     2 * LByzNodeAllowed(c) + 1
// }


function LMinQuorumSize(c:LConfiguration) : int
{
    |c.replica_ids|/2+1
}

function LByzQuorumSize(c:LConfiguration) : int
{
    (2 * |c.replica_ids|) / 3 + 1
}

lemma Lemma_TwoByzantineQuorumsIntersect(c: LConfiguration)
    ensures 2 * LByzQuorumSize(c) > |c.replica_ids|
{
   
}

lemma Lemma_TwoMinQuorumsIntersect(c: LConfiguration)
    ensures 2 * LMinQuorumSize(c) > |c.replica_ids|
{
   
}

predicate ReplicasDistinct(replica_ids:seq<NodeIdentity>, i:int, j:int)
{
  0 <= i < |replica_ids| && 0 <= j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j
}

predicate ReplicasIsUnique(replica_ids:seq<NodeIdentity>)
{
  forall i,j :: 0 <= i < |replica_ids| && 0 <= j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j
}

predicate WellFormedLConfiguration(c:LConfiguration)
{
  && 0 < |c.replica_ids|
  && (forall i, j :: ReplicasDistinct(c.replica_ids, i, j))
  && ReplicasIsUnique(c.replica_ids)
}

predicate IsReplicaIndex(idx:int, id:NodeIdentity, c:LConfiguration)
{
  && 0 <= idx < |c.replica_ids|
  && c.replica_ids[idx] == id
}

function GetReplicaIndex(id:NodeIdentity, c:LConfiguration):int
  requires id in c.replica_ids
  ensures  var idx := GetReplicaIndex(id, c);
            IsReplicaIndex(idx,id,c)
          //  0 <= idx < |c.replica_ids| && c.replica_ids[idx] == id
{
  FindIndexInSeq(c.replica_ids, id)
}

lemma lemma_DiffReplicaHasDiffIndex(id1:NodeIdentity, id2:NodeIdentity, c:LConfiguration)
  requires id1 != id2
  // requires ReplicasIsUnique(c.replica_ids)
  requires id1 in c.replica_ids && id2 in c.replica_ids
  ensures GetReplicaIndex(id1, c) != GetReplicaIndex(id2, c)
{

}

// lemma lemma_ReplicaIdxIsUnique(c:LConfiguration)

lemma lemma_GetReplicaIndexIsUnique(c:LConfiguration, idx:int)
  requires WellFormedLConfiguration(c)
  requires 0 <= idx < |c.replica_ids|
  ensures  GetReplicaIndex(c.replica_ids[idx], c) == idx
{
  var j := GetReplicaIndex(c.replica_ids[idx], c);
  assert ReplicasDistinct(c.replica_ids, idx, j);
}



} 
