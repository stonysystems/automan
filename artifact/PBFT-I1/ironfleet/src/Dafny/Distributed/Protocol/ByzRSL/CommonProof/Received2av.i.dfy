include "Assumptions.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"

module CommonProof__Received2av_i {

import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Actions_i
import opened CommonProof__Constants_i
import opened CommonProof__PacketSending_i
import opened Temporal__Temporal_s

lemma lemma_PacketInReceived2avWasSent(
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
  requires opn in b[i].replicas[replica_idx].replica.acceptor.received_2avs
  requires p in b[i].replicas[replica_idx].replica.acceptor.received_2avs[opn].received_2av_packets
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
  var s := b[i-1].replicas[replica_idx].replica.acceptor;
  var s' := b[i].replicas[replica_idx].replica.acceptor;

  if opn in s.received_2avs && p in s.received_2avs[opn].received_2av_packets
  {
    lemma_PacketInReceived2avWasSent(b, c, i-1, replica_idx, opn, p);
    assert p in b[i].environment.sentPackets;
    assert p.src in c.config.replica_ids;
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, replica_idx);
}

}
