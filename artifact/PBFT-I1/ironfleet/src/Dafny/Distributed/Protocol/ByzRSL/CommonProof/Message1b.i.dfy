include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "Message1c.i.dfy"
include "Message2b.i.dfy"
include "MaxBallot.i.dfy"
include "Votes.i.dfy"

module CommonProof__Message1b_i {
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Types_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened CommonProof__Message2b_i
import opened CommonProof__max_bal_i
import opened CommonProof__Votes_i
import opened CommonProof__Message1c_i
import opened Environment_s
import opened Temporal__Temporal_s

lemma lemma_1bMessageImplicationsForCAcceptor(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p:RslPacket
  ) returns (
  acceptor_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_1b?
  ensures  0 <= acceptor_idx < |c.config.replica_ids|
  ensures  0 <= acceptor_idx < |b[i].replicas|
  ensures  p.src == c.config.replica_ids[acceptor_idx]
  ensures  BalLeq(p.msg.bal_1b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal)
  ensures  var s := b[i].replicas[acceptor_idx].replica.acceptor;
           opn in p.msg.votes && opn >= s.log_truncation_point ==>
             && opn in s.votes
             && (|| BalLeq(p.msg.bal_1b, s.votes[opn].max_value_bal)
                || s.votes[opn] == Vote(p.msg.votes[opn].max_value_bal, p.msg.votes[opn].max_val))
  ensures  var s := b[i].replicas[acceptor_idx].replica.acceptor;
           opn !in p.msg.votes && opn >= s.log_truncation_point ==>
             || opn !in s.votes
             || (opn in s.votes && BalLeq(p.msg.bal_1b, s.votes[opn].max_value_bal));
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
    acceptor_idx := lemma_1bMessageImplicationsForCAcceptor(b, c, i-1, opn, p);
    var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
    var s' := b[i].replicas[acceptor_idx].replica.acceptor;

    if opn < s'.log_truncation_point
    {
      return;
    }
    if s'.log_truncation_point == s.log_truncation_point && s'.votes == s.votes
    {
      return;
    }

    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, acceptor_idx);
    assert opn >= s'.log_truncation_point >= s.log_truncation_point;
    if opn in p.msg.votes
    {
      lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, acceptor_idx);

      if s'.votes[opn].max_value_bal == s.votes[opn].max_value_bal
      {
        lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, s.votes[opn].max_value_bal, acceptor_idx);
      }
    }
    return;
  }

  var ios:seq<RslIo>;
  acceptor_idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p);

  var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
  var s' := b[i].replicas[acceptor_idx].replica.acceptor;
  if opn in s.votes && opn in s'.votes && s'.votes[opn].max_value_bal == s.votes[opn].max_value_bal
  {
    lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, s.votes[opn].max_value_bal, acceptor_idx);
  }
}

/**
同一节点发送的1b和2b，这个节点之前没收到过这个opn，所以其votes里不包含这个opn
如果1b没有opn，但是2b有，只能说明是在一个更大的bal里才收到了1c，触发了发送2b，所以要证明1b.bal<=2b.bal
证明：1b的bal小于等于2b的bal
证明逻辑：
1. 如果1b在i-1的状态里，找到发送1b的acceptor，找到发送2b的acceptor，证明是一个acceptor
2. 如果1b不在i-1的状态里，但是2b在（这可能吗？为啥能先发2b，再发1b，可能是同一个bal内的，但是这样它的vote里就有这个opn了啊，为什么1b里会没有呢？）
   找到发2b的acceptor，再找发1b的acceptor，证明是同一个acceptor
 */
lemma lemma_1bMessageWithoutOpnImplicationsFor2b(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p_1b:RslPacket,
  p_2b:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_1b in b[i].environment.sentPackets
  requires p_2b in b[i].environment.sentPackets
  requires p_1b.src in c.config.replica_ids
  requires p_1b.src == p_2b.src
  requires p_1b.msg.RslMessage_1b?
  requires p_2b.msg.RslMessage_2b?
  requires opn !in p_1b.msg.votes
  requires opn >= p_1b.msg.log_truncation_point
  requires p_2b.msg.opn_2b == opn
  ensures  BalLeq(p_1b.msg.bal_1b, p_2b.msg.bal_2b)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p_1b in b[i-1].environment.sentPackets
  {
    if p_2b in b[i-1].environment.sentPackets
    {
      lemma_1bMessageWithoutOpnImplicationsFor2b(b, c, i-1, opn, p_1b, p_2b);
    }
    else
    {
      var acceptor_idx := lemma_1bMessageImplicationsForCAcceptor(b, c, i-1, opn, p_1b);
      var acceptor_idx_alt, ios := lemma_ActionThatSends2bIsMaybeSend2b(b[i-1], b[i], p_2b);
      assert ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt);
      assert acceptor_idx == acceptor_idx_alt;
      assert BalLeq(p_1b.msg.bal_1b, b[i-1].replicas[acceptor_idx].replica.acceptor.max_bal);
      assert BalLeq(b[i-1].replicas[acceptor_idx].replica.acceptor.max_bal, b[i].replicas[acceptor_idx].replica.acceptor.max_bal);
      assert p_2b.msg.bal_2b == b[i-1].replicas[acceptor_idx].replica.acceptor.val_to_be_sent_2b.bal;
      assert b[i-1].replicas[acceptor_idx].replica.acceptor.val_to_be_sent_2b.bal == b[i-1].replicas[acceptor_idx].replica.acceptor.max_bal;
      assert p_2b.msg.bal_2b == b[i-1].replicas[acceptor_idx].replica.acceptor.max_bal;
      assert BalLeq(p_1b.msg.bal_1b, p_2b.msg.bal_2b);
    }
  }
  else
  {
    if p_2b in b[i-1].environment.sentPackets
    {
      /**
      1b 发生在 2b 之后，但是1b没有这个opn，怎么会发生？
       */
      var acceptor_idx := lemma_2bMessageImplicationsForCAcceptor(b, c, i-1, p_2b);
      // var acceptor_idx_alt, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
      // assert ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt);
      var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
      // assert opn >= p_1b.msg.log_truncation_point;
      assert p_2b.msg.opn_2b >= s.log_truncation_point;
      assert p_2b.msg.opn_2b in s.votes;
      // assert opn == p_2b.msg.opn_2b;
      assert opn !in s.votes;
      assert false;
    }
    else
    {
      var acceptor_idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
      assert LIoOpSend(p_1b) in ios;
      assert false;
    }
  }
}

/**
1b里有这个opn，有几种情况：
 1. 1b发生在2b前 => 1b.bal <= 2b.bal
 2. 1b发生在2b后, 并且1b发的不是2b这一轮选择的值，而是更大轮数被的val => 2b.bal < 1b.votes[opn].max_val_bal
 3. 1b发的就是2b所在轮选择的那个值 => 2b.bal == 1b.votes[opn].max_bal && 2b.val == 1b.votes[opn].max_val  
 */
lemma lemma_1bMessageWithOpnImplicationsFor2b(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p_1b:RslPacket,
  p_2b:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_1b in b[i].environment.sentPackets
  requires p_2b in b[i].environment.sentPackets
  requires p_1b.src in c.config.replica_ids
  requires p_1b.src == p_2b.src
  requires p_1b.msg.RslMessage_1b?
  requires p_2b.msg.RslMessage_2b?
  requires opn in p_1b.msg.votes
  requires opn >= p_1b.msg.log_truncation_point
  requires p_2b.msg.opn_2b == opn
  ensures  || BalLeq(p_1b.msg.bal_1b, p_2b.msg.bal_2b)
           || (p_2b.msg.bal_2b == p_1b.msg.votes[opn].max_value_bal && p_2b.msg.val_2b == p_1b.msg.votes[opn].max_val)
           || BalLt(p_2b.msg.bal_2b, p_1b.msg.votes[opn].max_value_bal)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p_1b in b[i-1].environment.sentPackets
  {
    if p_2b in b[i-1].environment.sentPackets
    {
      lemma_1bMessageWithOpnImplicationsFor2b(b, c, i-1, opn, p_1b, p_2b);
    }
    else
    {
      /**
      1b 发生在 2b之前
       */
      var acceptor_idx := lemma_1bMessageImplicationsForCAcceptor(b, c, i-1, opn, p_1b);
      var acceptor_idx_alt, ios := lemma_ActionThatSends2bIsMaybeSend2b(b[i-1], b[i], p_2b);
      assert ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt);
    }
  }
  else
  {
    if p_2b in b[i-1].environment.sentPackets
    {
      /**
      1b 发生在 2b之后
      两种情况：
      1. 1b发的就是2b所在轮选择的那个值 => 2b.bal == 1b.votes[opn].max_bal && 2b.val == 1b.votes[opn].max_val  
      2. 1b发生在2b后, 并且1b发的不是2b这一轮选择的值，而是更大轮数被的val => 2b.bal < 1b.votes[opn].max_val_bal
       */
      var acceptor_idx := lemma_2bMessageImplicationsForCAcceptor(b, c, i-1, p_2b);
      var acceptor_idx_alt, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
      assert ReplicasDistinct(c.config.replica_ids, acceptor_idx, acceptor_idx_alt);
      var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
      // assert p_2b.msg.opn_2b >= s.log_truncation_point;
      assert p_2b.msg.opn_2b in s.votes;
      assert BalLeq(p_2b.msg.bal_2b, s.votes[p_2b.msg.opn_2b].max_value_bal);
      assert (s.votes[p_2b.msg.opn_2b].max_value_bal == p_2b.msg.bal_2b ==> s.votes[p_2b.msg.opn_2b].max_val == p_2b.msg.val_2b);
    }
    else
    {
      var acceptor_idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
      assert LIoOpSend(p_1b) in ios;
      assert false;
    }
  }
}

lemma lemma_Vote1bMessageIsFromEarlierBallot(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_1b?
  requires opn in p.msg.votes
  ensures  BalLt(p.msg.votes[opn].max_value_bal, p.msg.bal_1b)
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
    lemma_Vote1bMessageIsFromEarlierBallot(b, c, i-1, opn, p);
    return;
  }

  var idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p);
  lemma_VotePrecedesMaxBal(b, c, i-1, idx, opn);
}

lemma lemma_1bMessageWithOpnImplies1cSent(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  p_1b:RslPacket
  ) returns (
  p_1c:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_1b in b[i].environment.sentPackets
  requires p_1b.src in c.config.replica_ids
  requires p_1b.msg.RslMessage_1b?
  requires opn in p_1b.msg.votes
  ensures  p_1c in b[i].environment.sentPackets
  ensures  p_1c.src in c.config.replica_ids
  ensures  p_1c.msg.RslMessage_1c?
  ensures  p_1c.msg.opn_1c == opn
  ensures  p_1c.msg.bal_1c == p_1b.msg.votes[opn].max_value_bal
  ensures  p_1c.msg.val_1c == p_1b.msg.votes[opn].max_val
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  if p_1b in b[i-1].environment.sentPackets
  {
    p_1c := lemma_1bMessageWithOpnImplies1cSent(b, c, i-1, opn, p_1b);
    return;
  }

  var idx, ios := lemma_ActionThatSends1bIsProcess1a(b[i-1], b[i], p_1b);
  p_1c := lemma_Find1cThatCausedVote(b, c, i-1, idx, opn);
}

}
