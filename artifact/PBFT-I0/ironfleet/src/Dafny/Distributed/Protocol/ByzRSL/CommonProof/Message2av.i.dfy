include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"

module CommonProof__Message2av_i {
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Proposer_i
import opened LiveByzRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened Temporal__Temporal_s
import opened Environment_s

lemma lemma_2avMessageHasCorresponding1cMessage(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    p_2av:RslPacket
) returns (
    p_1c:RslPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i
    requires p_2av in b[i].environment.sentPackets
    requires p_2av.src in c.config.replica_ids
    requires p_2av.msg.RslMessage_2av?
    ensures  p_1c in b[i].environment.sentPackets
    ensures  p_1c.src in c.config.replica_ids
    ensures  p_1c.msg.RslMessage_1c?
    ensures  p_1c.msg.opn_1c == p_2av.msg.opn_2av
    ensures  p_1c.msg.bal_1c == p_2av.msg.bal_2av
    ensures  p_1c.msg.val_1c == p_2av.msg.val_2av
    decreases i 
{
    if i == 0
    {
      return;
    }

    if p_2av in b[i-1].environment.sentPackets
    {
        p_1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i-1, p_2av);
        lemma_PacketStaysInSentPackets(b, c, i-1, i, p_1c);
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i-1);

    var acceptor_idx, ios := lemma_ActionThatSends2avIsProcess1c(b[i-1], b[i], p_2av);
    p_1c := ios[0].r;
}

// lemma lemma_2avMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(
//   b:Behavior<RslState>,
//   c:LConstants,
//   i:int,
//   p1:RslPacket,
//   p2:RslPacket
// )
//   requires IsValidBehaviorPrefix(b, c, i)
//   requires 0 < i
//   requires p1 in b[i].environment.sentPackets
//   requires p2 in b[i].environment.sentPackets
//   requires p1.src in c.config.replica_ids
//   requires p2.src in c.config.replica_ids
//   requires p1.msg.RslMessage_2av?
//   requires p2.msg.RslMessage_2av?
//   requires p1.msg.opn_2av == p2.msg.opn_2av
//   requires p1.msg.bal_2av == p2.msg.bal_2av
//   requires p2 in b[i-1].environment.sentPackets ==> p1 in b[i-1].environment.sentPackets
//   ensures  p1.msg.val_2av == p2.msg.val_2av
//   decreases 2 * i
// {
//   // lemma_AssumptionsMakeValidTransition(b, c, i-1);
//   // lemma_ConstantsAllConsistent(b, c, i);
//   // lemma_ConstantsAllConsistent(b, c, i-1);

//   // if p2 in b[i-1].environment.sentPackets
//   // {
//   //   // Both packets had already been sent by i-1, so we induction.
//   //   lemma_2avMessagesFromSameBallotAndOperationMatch(b, c, i-1, p1, p2);
//   //   return;
//   // }

//   // var proposer_idx, ios := lemma_ActionThatSends2avIsProcess1c(b[i-1], b[i], p2);

//   // if p1 !in b[i-1].environment.sentPackets
//   // {
//   //   // Both packets were sent in step i-1, so observe that any two packets sent in the same step
//   //   // have the same value.
//   //   assert LIoOpSend(p1) in ios;
//   //   assert LIoOpSend(p2) in ios;
//   //   return;
//   // }

//   // // Note the implications on processor state for p1, since once p1 is sent we
//   // // won't be able to send p2.
//   // var alt_proposer_idx := lemma_2aMessageImplicationsForProposerState(b, c, i-1, p1);

//   // // Note the implications on processor state for p2, just to notice that they
//   // // use the same replica index.
//   // var alt2_proposer_idx := lemma_2aMessageImplicationsForProposerState(b, c, i, p2);
//   // assert alt_proposer_idx == alt2_proposer_idx;
//   // assert ReplicasDistinct(c.config.replica_ids, proposer_idx, alt_proposer_idx);
//   // assert proposer_idx == alt_proposer_idx;
//   // assert false;
// }


// lemma lemma_2avMessagesFromSameBallotAndOperationMatch(
//   b:Behavior<RslState>,
//   c:LConstants,
//   i:int,
//   p1:RslPacket,
//   p2:RslPacket
// )
//   requires IsValidBehaviorPrefix(b, c, i)
//   requires 0 <= i
//   requires p1 in b[i].environment.sentPackets
//   requires p2 in b[i].environment.sentPackets
//   requires p1.src in c.config.replica_ids
//   requires p2.src in c.config.replica_ids
//   requires p1.msg.RslMessage_2av?
//   requires p2.msg.RslMessage_2av?
//   requires p1.msg.opn_2av == p2.msg.opn_2av
//   requires p1.msg.bal_2av == p2.msg.bal_2av
//   ensures  p1.msg.val_2av == p2.msg.val_2av
//   decreases 2 * i + 1
// {
//   if i == 0
//   {
//     return;
//   }

//   if p2 in b[i-1].environment.sentPackets && p1 !in b[i-1].environment.sentPackets
//   {
//     lemma_2avMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p2, p1);
//   }
//   else
//   {
//     lemma_2avMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p1, p2);
//   }
// }
}