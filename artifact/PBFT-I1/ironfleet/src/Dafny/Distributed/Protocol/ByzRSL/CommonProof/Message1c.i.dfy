include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "MaxBallotISent1a.i.dfy"
include "Received1b.i.dfy"
include "Message2b.i.dfy"
include "Message2av.i.dfy"
include "QuorumOf2avs.i.dfy"

module CommonProof__Message1c_i {
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Proposer_i
import opened LiveByzRSL__Types_i
import opened LiveByzRSL__CheckValSafety_i
import opened LiveByzRSL__Replica_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened CommonProof__max_balISent1a_i
import opened CommonProof__Received1b_i
import opened CommonProof__Message2b_i
import opened CommonProof__Message2av_i
import opened CommonProof__QuorumOf2avs_i
import opened Temporal__Temporal_s
import opened Environment_s

lemma lemma_1cMessageImplicationsForProposerState(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
) returns (
    proposer_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_1c?
  ensures  0 <= proposer_idx < |c.config.replica_ids|
  ensures  0 <= proposer_idx < |b[i].replicas|
  ensures  p.src == c.config.replica_ids[proposer_idx]
  ensures  p.msg.bal_1c.proposer_id == proposer_idx
  ensures  var s := b[i].replicas[proposer_idx].replica.proposer;
            || BalLt(p.msg.bal_1c, s.max_ballot_i_sent_1a)
            || (&& s.max_ballot_i_sent_1a == p.msg.bal_1c
                  && s.current_state != 1
                  && s.next_operation_number_to_propose > p.msg.opn_1c)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p in b[i-1].environment.sentPackets
  {
    proposer_idx := lemma_1cMessageImplicationsForProposerState(b, c, i-1, p);
    var s := b[i-1].replicas[proposer_idx].replica.proposer;
    var s' := b[i].replicas[proposer_idx].replica.proposer;
    if s' != s
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, proposer_idx);
    }
    return;
  }

  var ios:seq<RslIo>;
  proposer_idx, ios := lemma_ActionThatSends1cIsMaybeNominateValueAndSend1c(b[i-1], b[i], p);
  lemma_max_balISent1aHasMeAsProposer(b, c, i-1, proposer_idx);
}

lemma lemma_1cMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p1:RslPacket,
  p2:RslPacket
)
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 < i
  requires p1 in b[i].environment.sentPackets
  requires p2 in b[i].environment.sentPackets
  requires p1.src in c.config.replica_ids
  requires p2.src in c.config.replica_ids
  requires p1.msg.RslMessage_1c?
  requires p2.msg.RslMessage_1c?
  requires p1.msg.opn_1c == p2.msg.opn_1c
  requires p1.msg.bal_1c == p2.msg.bal_1c
  requires p2 in b[i-1].environment.sentPackets ==> p1 in b[i-1].environment.sentPackets
  ensures  p1.msg.val_1c == p2.msg.val_1c
  decreases 2 * i
{
  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p2 in b[i-1].environment.sentPackets
  {
    // Both packets had already been sent by i-1, so we induction.
    lemma_1cMessagesFromSameBallotAndOperationMatch(b, c, i-1, p1, p2);
    return;
  }

  var proposer_idx, ios := lemma_ActionThatSends1cIsMaybeNominateValueAndSend1c(b[i-1], b[i], p2);

  if p1 !in b[i-1].environment.sentPackets
  {
    // Both packets were sent in step i-1, so observe that any two packets sent in the same step
    // have the same value.
    assert LIoOpSend(p1) in ios;
    assert LIoOpSend(p2) in ios;
    return;
  }

  // Note the implications on processor state for p1, since once p1 is sent we
  // won't be able to send p2.
  var alt_proposer_idx := lemma_1cMessageImplicationsForProposerState(b, c, i-1, p1);

  // Note the implications on processor state for p2, just to notice that they
  // use the same replica index.
  var alt2_proposer_idx := lemma_1cMessageImplicationsForProposerState(b, c, i, p2);
  assert alt_proposer_idx == alt2_proposer_idx;
  assert ReplicasDistinct(c.config.replica_ids, proposer_idx, alt_proposer_idx);
  assert proposer_idx == alt_proposer_idx;
  assert false;
}

lemma lemma_1cMessagesFromSameBallotAndOperationMatch(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    p1:RslPacket,
    p2:RslPacket
  )
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i
    requires p1 in b[i].environment.sentPackets
    requires p2 in b[i].environment.sentPackets
    requires p1.src in c.config.replica_ids
    requires p2.src in c.config.replica_ids
    requires p1.msg.RslMessage_1c?
    requires p2.msg.RslMessage_1c?
    requires p1.msg.opn_1c == p2.msg.opn_1c
    requires p1.msg.bal_1c == p2.msg.bal_1c
    ensures  p1.msg.val_1c == p2.msg.val_1c
    decreases 2 * i + 1
  {
    if i == 0
    {
      return;
    }

    if p2 in b[i-1].environment.sentPackets && p1 !in b[i-1].environment.sentPackets
    {
      lemma_1cMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p2, p1);
    }
    else
    {
      lemma_1cMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p1, p2);
    }
  }

lemma lemma_1cMessageHas1bQuorumPermittingIt(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    p:RslPacket
) returns (
    q:seq<RslPacket>
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i
    requires p in b[i].environment.sentPackets
    requires p.src in c.config.replica_ids
    requires p.msg.RslMessage_1c?
    // ensures  q <= b[i].environment.sentPackets
    ensures forall p :: p in q ==> p in b[i].environment.sentPackets
    ensures  |q| >= LByzQuorumSize(c.config)
    ensures  LIsAfterLogTruncationPoint(p.msg.opn_1c, q)
    ensures  LSetOfMessage1bAboutBallot(q, p.msg.bal_1c)
    ensures  var byzq := LByzQuorumSize(c.config);
            //  var msg1bs := Convert1bPacketsSeqToMsgSeq(q);
             var wq := LMinQuorumSize(c.config);
            LAllAcceptorsHadNoProposal(q, p.msg.opn_1c) || LValIsSafeAt(p.msg.val_1c, /*p.msg.bal_1c,*/ q, p.msg.opn_1c, byzq, wq)
    ensures  forall i, j :: 0 <= i < j < |q| ==> q[i] != q[j] // 这个能否满足呢？
    ensures  forall p1, p2 :: p1 in q && p2 in q && p1 != p2 ==> p1.src != p2.src
    ensures  forall p1 :: p1 in q ==> p1.src in c.config.replica_ids
{
    if i == 0
    {
        return;
    }

    if p in b[i-1].environment.sentPackets
    {
        q := lemma_1cMessageHas1bQuorumPermittingIt(b, c, i-1, p);
        lemma_PacketSeqStaysInSentPackets(b, c, i-1, i, q);
        return;
    }

    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    var idx, ios := lemma_ActionThatSends1cIsMaybeNominateValueAndSend1c(b[i-1], b[i], p);
    q := b[i-1].replicas[idx].replica.proposer.received_1b_packets;

    

    forall p_1b | p_1b in q
        ensures p_1b in b[i].environment.sentPackets
    {
        lemma_PacketInReceived1bWasSent(b, c, i-1, idx, p_1b);
        lemma_PacketStaysInSentPackets(b, c, i-1, i, p_1b);
    }

    lemma_Received1bPacketsAreFrommax_balISent1a(b, c, i-1, idx);

    assert forall p1, p2 :: p1 in q && p2 in q && p1 != p2 ==> p1.src != p2.src;
}

  lemma lemma_1cMessageHasValidBallot(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    p:RslPacket
  )
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i
    requires p in b[i].environment.sentPackets
    requires p.src in c.config.replica_ids
    requires p.msg.RslMessage_1c?
    ensures  p.msg.bal_1c.seqno >= 0
    ensures  0 <= p.msg.bal_1c.proposer_id < |c.config.replica_ids|
  {
    if i == 0
    {
      return;
    }

    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
      lemma_1cMessageHasValidBallot(b, c, i-1, p);
      return;
    }

    var idx, ios := lemma_ActionThatSends1cIsMaybeNominateValueAndSend1c(b[i-1], b[i], p);
    lemma_max_balISent1aHasMeAsProposer(b, c, i-1, idx);
  }

  lemma lemma_Find1cThatCausedVote(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    idx:int,
    opn:OperationNumber
  ) returns (
      p:RslPacket
    )
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i
    requires 0 <= idx < |b[i].replicas|
    requires opn in b[i].replicas[idx].replica.acceptor.votes
    ensures  p in b[i].environment.sentPackets
    ensures  p.src in c.config.replica_ids
    ensures  p.msg.RslMessage_1c?
    ensures  p.msg.opn_1c == opn
    ensures  p.msg.val_1c == b[i].replicas[idx].replica.acceptor.votes[opn].max_val
    ensures  p.msg.bal_1c == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal
    decreases i
  {
    if i == 0
    {
      return;
    }

    lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
    lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    var s := b[i-1].replicas[idx].replica.acceptor;
    var s' := b[i].replicas[idx].replica.acceptor;

    

    if opn in s.votes && s'.votes[opn] == s.votes[opn]
    {
      p := lemma_Find1cThatCausedVote(b, c, i-1, idx, opn);
      return;
    }

    var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;
    assert nextActionIndex == 0 || nextActionIndex == 5;

    if nextActionIndex == 0 {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
      p := ios[0].r;
      assert  p in b[i].environment.sentPackets;
      assert  p.src in c.config.replica_ids;
      assert  p.msg.RslMessage_1c?;
      assert  p.msg.opn_1c == opn;
      assert  p.msg.val_1c == b[i].replicas[idx].replica.acceptor.votes[opn].max_val;
      assert  p.msg.bal_1c == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal;
    }
    else
    {
      var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
      var packets := ExtractSentPacketsFromIos(ios);
      var p_2b := packets[0];
      var vbal := s.val_to_be_sent_2b.bal;
      var vval := s.val_to_be_sent_2b.v;
      assert p_2b.msg.RslMessage_2b?;
      assert p_2b.msg.bal_2b == vbal;
      assert p_2b.msg.val_2b == vval;
      var q2avs := lemma_2bSentIsMaybeSend2b(b, c, i-1, p_2b, idx, ios);
      assert IsValidQuorumOf2avs(b[i], q2avs);
      var idx2 :| idx2 in q2avs.indices;
      var p_2av := q2avs.packets[idx2];
      // assert packet_2av.msg.RslMessage_2av?;
      // assert packet_2av.msg.val_2av == packet_2b.msg.val_2b;
      // assert packet_2av.msg.val_2av == batch;

      // p := lemma_RequestIn2aMessageHasCorrespondingRequestMessage(b, c, i, packet_2a, req_num);
      p := lemma_2avMessageHasCorresponding1cMessage(b, c, i, p_2av);

    }
  }
}