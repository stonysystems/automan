include "Assumptions.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"

module CommonProof__Received2b_i {

import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__PacketSending_i
import opened Temporal__Temporal_s

lemma lemma_PacketInReceived2bWasSent(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  replica_idx:int,
  opn:OperationNumber,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= replica_idx < |b[i].replicas|
  requires opn in b[i].replicas[replica_idx].replica.learner.unexecuted_learner_state
  requires p in b[i].replicas[replica_idx].replica.learner.unexecuted_learner_state[opn].received_2bs
  ensures  p in b[i].environment.sentPackets
  ensures  p.src in c.config.replica_ids
{
  if i == 0
  {
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  var s := b[i-1].replicas[replica_idx].replica.learner;
  var s' := b[i].replicas[replica_idx].replica.learner;

  if opn in s.unexecuted_learner_state && p in s.unexecuted_learner_state[opn].received_2bs
  {
    lemma_PacketInReceived2bWasSent(b, c, i-1, replica_idx, opn, p);
    assert p in b[i].environment.sentPackets;
    assert p.src in c.config.replica_ids;
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, replica_idx);
}

}
