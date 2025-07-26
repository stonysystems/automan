include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"

module CommonProof__AcceptorState_i{
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened Temporal__Temporal_s
import opened Concrete_NodeIdentity_i

lemma lemma_Received2avMessageSendersAlwaysValidReplicas(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  acceptor_idx:int,
  opn:OperationNumber
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= acceptor_idx < |b[i].replicas|
  requires opn in b[i].replicas[acceptor_idx].replica.acceptor.received_2avs
  // ensures  forall sender :: sender in b[i].replicas[acceptor_idx].replica.acceptor.received_2avs[opn].received_2av_message_senders
  //                     ==> sender in c.config.replica_ids
  ensures forall p :: p in b[i].replicas[acceptor_idx].replica.acceptor.received_2avs[opn].received_2av_packets
                  ==> p.src in c.config.replica_ids
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);

  var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
  var s' := b[i].replicas[acceptor_idx].replica.acceptor;

  forall p | p in s'.received_2avs[opn].received_2av_packets
    ensures p.src in c.config.replica_ids
  {
    if opn in s.received_2avs && p in s.received_2avs[opn].received_2av_packets
    {
      lemma_Received2avMessageSendersAlwaysValidReplicas(b, c, i-1, acceptor_idx, opn);
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, acceptor_idx);
    }
  }
}

// lemma lemma_GetSent2avMessageFromAcceptorState(
//   b:Behavior<RslState>,
//   c:LConstants,
//   i:int,
//   acceptor_idx:int,
//   opn:OperationNumber,
//   sender:NodeIdentity
//   ) returns (
//   sender_idx:int,
//   p:RslPacket
//   )
//   requires IsValidBehaviorPrefix(b, c, i)
//   requires 0 <= i
//   requires 0 <= acceptor_idx < |b[i].replicas|
//   requires opn in b[i].replicas[acceptor_idx].replica.acceptor.received_2avs
//   requires sender in b[i].replicas[acceptor_idx].replica.acceptor.received_2avs[opn].received_2av_message_senders
//   ensures  0 <= sender_idx < |c.config.replica_ids|
//   ensures  p in b[i].environment.sentPackets
//   ensures  p.src == sender == c.config.replica_ids[sender_idx]
//   ensures  p.msg.RslMessage_2av?
//   ensures  p.msg.opn_2av == opn
// //   ensures  p.msg.bal_2b == b[i].replicas[acceptor_idx].replica..max_ballot_seen
// //   ensures  p.msg.val_2b == b[i].replicas[acceptor_idx].replica.learner.unexecuted_learner_state[opn].candidate_learned_value
//   decreases i
// {
//   if i == 0
//   {
//     return;
//   }

//   lemma_ReplicaConstantsAllConsistent(b, c, i, acceptor_idx);
//   lemma_ReplicaConstantsAllConsistent(b, c, i-1, acceptor_idx);
//   lemma_AssumptionsMakeValidTransition(b, c, i-1);

//   var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
//   var s' := b[i].replicas[acceptor_idx].replica.acceptor;

//   if s'.max_bal == s.max_bal && s'.received_2avs == s.received_2avs
//   {
//     sender_idx, p := lemma_GetSent2avMessageFromAcceptorState(b, c, i-1, acceptor_idx, opn, sender);
//     lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
//     return;
//   }

//   if && opn in s.received_2avs
//      && sender in s.received_2avs[opn].received_2av_message_senders
//   {
//     sender_idx, p := lemma_GetSent2avMessageFromAcceptorState(b, c, i-1, acceptor_idx, opn, sender);
//     lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
//     return;
//   }

//   var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, acceptor_idx);
//   var nextActionIndex := b[i-1].replicas[acceptor_idx].nextActionIndex;
//   assert nextActionIndex == 0;
//   assert ios[0].LIoOpReceive?;
//   p := ios[0].r;
//   sender_idx := GetReplicaIndex(p.src, c.config);
// }
}