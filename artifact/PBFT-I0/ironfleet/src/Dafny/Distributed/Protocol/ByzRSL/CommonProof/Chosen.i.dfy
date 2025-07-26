include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "LearnerState.i.dfy"
include "Quorum.i.dfy"
include "QuorumOf2avs.i.dfy"
include "Message1b.i.dfy"
include "Message1c.i.dfy"
include "Message2av.i.dfy"
include "Message2b.i.dfy"
include "Received2b.i.dfy"

module CommonProof__Chosen_i {

import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Executor_i
import opened LiveByzRSL__Message_i
import opened LiveByzRSL__Proposer_i
import opened LiveByzRSL__Learner_i
import opened LiveByzRSL__Types_i
import opened LiveByzRSL__CheckValSafety_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
import opened CommonProof__LearnerState_i
import opened CommonProof__Quorum_i
import opened CommonProof__QuorumOf2avs_i
import opened CommonProof__Message1b_i
import opened CommonProof__Message1c_i
import opened CommonProof__Received2b_i
import opened CommonProof__Message2av_i
import opened CommonProof__Message2b_i
import opened Concrete_NodeIdentity_i
import opened Temporal__Temporal_s
import opened Collections__Sets_i
import opened Environment_s
import opened Collections__CountMatches_i

datatype QuorumOf2bs = QuorumOf2bs(c:LConstants, indices:set<int>, packets:seq<RslPacket>, bal:Ballot, opn:OperationNumber, v:RequestBatch)

predicate IsValidQuorumOf2bs(
  ps:RslState,
  q:QuorumOf2bs
  )
{
  && |q.indices| >= LMinQuorumSize(ps.constants.config)
  && |q.packets| == |ps.constants.config.replica_ids|
  && (forall idx :: idx in q.indices ==> && 0 <= idx < |ps.constants.config.replica_ids|
                                 && var p := q.packets[idx];
                                   && p.src == ps.constants.config.replica_ids[idx]
                                   && p.msg.RslMessage_2b?
                                   && p.msg.opn_2b == q.opn
                                   && p.msg.val_2b == q.v
                                   && p.msg.bal_2b == q.bal
                                   && p in ps.environment.sentPackets)
}

lemma lemma_QuorumOf2bsStaysValid(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  j:int,
  q:QuorumOf2bs
  )
  requires IsValidBehaviorPrefix(b, c, j)
  requires IsValidQuorumOf2bs(b[i], q)
  requires 0 <= i <= j
  ensures  IsValidQuorumOf2bs(b[j], q)
{
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, j);

  forall idx | idx in q.indices
    ensures q.packets[idx] in b[j].environment.sentPackets
  {
    lemma_PacketStaysInSentPackets(b, c, i, j, q.packets[idx]);
  }
}

function ConvertSeqToSet<X(!new)>(xs:seq<X>):set<X>
  requires forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
  ensures  forall x :: x in xs <==> x in ConvertSeqToSet(xs)
  // ensures |xs| == |ConvertSeqToSet(xs)|
{
  set x | x in xs :: x
}

lemma lemma_SeqToSetLengthNotChange<X(!new)>(xs: seq<X>)
  requires forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
  ensures |xs| == |ConvertSeqToSet(xs)|
{
  if |xs| == 0 {
    // Base case: An empty sequence converts to an empty set
    assert ConvertSeqToSet(xs) == {};
  } else {
    // Inductive step: assume the lemma holds for xs[1..], prove for xs
    var rest := xs[1..];
    var firstElem := xs[0];
    
    // Recursive call on the tail of xs
    lemma_SeqToSetLengthNotChange(rest);
    assert |rest| == |ConvertSeqToSet(rest)|;

    // Check that firstElem is not in the rest of the sequence
    assert !(firstElem in rest);
    assert ConvertSeqToSet(xs) == ConvertSeqToSet(rest) + {firstElem};

    // The size of ConvertSeqToSet(xs) is the size of ConvertSeqToSet(rest) + 1
    assert |ConvertSeqToSet(xs)| == |ConvertSeqToSet(rest)| + 1;
    assert |xs| == |rest| + 1;
  }
}

// /**
// 验证目标：一个q2bs的val和一个bal更大的q2avs的val一样

// q2avs2 -> 
// 2b -> packet2b_overlap
// 1b -> packet1b_overlap

// q2av -> q2av
// 1b2 -> chosen_packet1b
// q2av3 -> previous_packet2a （从1b2推出来，是之前bal发的2a）

// 步骤：
// 1. 找到q2avs中的一个2a
// 2. 找到2a对应的1b set
// 3. 找到1b set和q2bs的交集节点
// 4. 找到这个交集发出的 2b 和 1b，2b 应该是早于1b的
// 5. 找到决定2a val的那个1b （1b2）
// 6. 找到1b2 对应的 q2avs3，也就是导致这次投票的2av
// 7. 如果q2bs 和 q2avs2的bal一样，说明在这个bal达成共识的
//    此时找到2b对应的 q2avs3，证明q2avs2 和 q2avs3的val一样
// 8. 如果q2bs的bal和2a3的bal不一样，证明达成共识的bal还要更早
//    通过q2avs3为输入，递归往前匹配
//  */
// lemma lemma_ChosenQuorumAnd2avFromLaterBallotMatchValues(
//   b:Behavior<RslState>,
//   c:LConstants,
//   i:int,
//   quorum_of_2bs:QuorumOf2bs,
//   q2av:QuorumOf2avs
//   )
//   requires IsValidBehaviorPrefix(b, c, i)
//   requires 0 <= i
//   requires IsValidQuorumOf2bs(b[i], quorum_of_2bs)
//   requires IsValidQuorumOf2avs(b[i], q2av)
//   // requires packet2a in b[i].environment.sentPackets
//   // requires packet2a.src in c.config.replica_ids
//   // requires packet2a.msg.RslMessage_2av?
//   requires quorum_of_2bs.opn == q2av.opn
//   requires BalLt(quorum_of_2bs.bal, q2av.bal)
//   ensures  quorum_of_2bs.v == q2av.v
//   decreases q2av.bal.seqno, q2av.bal.proposer_id
// {
//   lemma_ConstantsAllConsistent(b, c, i);

//   var opn := quorum_of_2bs.opn;

//   var idx :| idx in q2av.indices;
//   var p2av := q2av.packets[idx];
//   var p1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i, p2av);
//   var q1bs := lemma_1cMessageHas1bQuorumPermittingIt(b, c, i, p1c);
//   assert p2av.msg.val_2av == p1c.msg.val_1c;

//   var q1bmsgs := Convert1bPacketsSeqToMsgSeq(q1bs);
//   assert |q1bs| >= LByzQuorumSize(c.config);
//   var quorum_of_1bs := ConvertSeqToSet(q1bs);
//   assert |quorum_of_1bs| >= LByzQuorumSize(c.config);
//   // var quorum_of_1bs := lemma_2aMessageHas1bQuorumPermittingIt(b, c, i, packet2a);
//   var quorum_of_1bs_indices := lemma_GetIndicesFromPackets(quorum_of_1bs, c.config);
//   assert |quorum_of_1bs_indices| >= LByzQuorumSize(c.config);
//   assert |quorum_of_2bs.indices| >= LMinQuorumSize(c.config);

//   var overlap_idx := lemma_QuorumIndexOverlap(quorum_of_1bs_indices, quorum_of_2bs.indices, |c.config.replica_ids|);
//   var packet1b_overlap :| packet1b_overlap in quorum_of_1bs && packet1b_overlap.src == c.config.replica_ids[overlap_idx];
//   var packet2b_overlap := quorum_of_2bs.packets[overlap_idx];

//   // var s := b[i].replicas[]

//   var byzq := LByzQuorumSize(c.config);
//   var wq := LMinQuorumSize(c.config);

//   if opn !in packet1b_overlap.msg.votes
//   {
//     lemma_1bMessageWithoutOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);
//     assert false;
//   }

//   var val := p1c.msg.val_1c;
//   assert LValIsSafeAt(val, q1bmsgs, opn, byzq, wq);
//   assert exists p :: p in q1bs && opn in p.msg.votes && p.msg.votes[opn].max_val == val;

//   var chosen_packet1b :| 
//       && chosen_packet1b in q1bs
//       && opn in chosen_packet1b.msg.votes
//       && LValIsSafeAt(chosen_packet1b.msg.votes[opn].max_val, q1bmsgs, opn, byzq, wq);
//   lemma_Vote1bMessageIsFromEarlierBallot(b, c, i, opn, chosen_packet1b);

//   lemma_1bMessageWithOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);

//   var previous_packet1c := lemma_1bMessageWithOpnImplies1cSent(b, c, i, opn, chosen_packet1b);
//   assert BalLt(previous_packet1c.msg.bal_1c, p2av.msg.bal_2av);

//   if quorum_of_2bs.bal == previous_packet1c.msg.bal_1c
//   {
//     var q2av_overlap := lemma_2bSentIsAllowed(b, c, i, packet2b_overlap);
//     var idx2 :| idx2 in q2av_overlap.indices;
//     var packet2av_overlap := q2av_overlap.packets[idx2];
//     var packet1c_overlap := lemma_2avMessageHasCorresponding1cMessage(b, c, i, packet2av_overlap);
//     lemma_1cMessagesFromSameBallotAndOperationMatch(b, c, i, packet1c_overlap, previous_packet1c);
//   }
//   else
//   {
//     lemma_1cMessageHasValidBallot(b, c, i, p1c);
//     // lemma_ChosenQuorumAnd2avFromLaterBallotMatchValues(b, c, i, quorum_of_2bs, )
//   }

//   // var highestballot_in_1b_set :| LValIsHighestNumberedProposalAtBallot(packet2a.msg.val_2a, highestballot_in_1b_set, quorum_of_1bs, opn);
//   // assert BalLeq(packet1b_overlap.msg.votes[opn].max_value_bal, highestballot_in_1b_set);
//   // var packet1b_highestballot :| && packet1b_highestballot in quorum_of_1bs
//   //                               && opn in packet1b_highestballot.msg.votes
//   //                               && packet1b_highestballot.msg.votes[opn] == Vote(highestballot_in_1b_set, packet2a.msg.val_2a);
//   // lemma_Vote1bMessageIsFromEarlierBallot(b, c, i, opn, packet1b_highestballot);

//   // lemma_1bMessageWithOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);

//   // var previous_packet2a := lemma_1bMessageWithOpnImplies2aSent(b, c, i, opn, packet1b_highestballot);
//   // assert BalLt(previous_packet2a.msg.bal_2a, packet2a.msg.bal_2a);

//   // if quorum_of_2bs.bal == previous_packet2a.msg.bal_2a
//   // {
//   //   var packet2a_overlap := lemma_2bMessageHasCorresponding2aMessage(b, c, i, packet2b_overlap);
//   //   lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i, packet2a_overlap, previous_packet2a);
//   // }
//   // else
//   // {
//   //   lemma_2aMessageHasValidBallot(b, c, i, packet2a); // to demonstrate decreases values are >= 0
//   //   lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues(b, c, i, quorum_of_2bs, previous_packet2a);
//   // }
// }

lemma lemma_Convert1bPacketsSeqToMsgSeqIsConsistent(q1bs:seq<RslPacket>, q1bmsgs:seq<RslMessage>)
  requires LSeqOfMessage1b(q1bs)
  requires forall p :: p in q1bs ==> p.msg.RslMessage_1b?
  requires q1bmsgs == Convert1bPacketsSeqToMsgSeq(q1bs)
  ensures forall i :: 0 <= i < |q1bs| ==> q1bmsgs[i] == q1bs[i].msg
{
  reveal_Convert1bPacketsSeqToMsgSeq();

  if |q1bs| == 0 {
      assert q1bmsgs == [];
  } else {
      // Base case for index 0
      assert q1bmsgs[0] == q1bs[0].msg;

      // Recursive case: q1bmsgs[1..] == Convert1bPacketsSeqToMsgSeq(q1bs[1..])
      lemma_Convert1bPacketsSeqToMsgSeqIsConsistent(q1bs[1..], q1bmsgs[1..]);
  }
}

lemma lemma_LValIsSafeAtImpliesLValIsHighestNumberedProposalAtBallot(v:RequestBatch, /*b:Ballot,*/ msg1bs:seq<RslPacket>, opn:OperationNumber, byzq:int, wq:int)
  requires forall m :: m in msg1bs ==> m.msg.RslMessage_1b?
  requires LValIsSafeAt(v, msg1bs, opn, byzq, wq)
  requires wq > 0
  ensures (exists p :: p in msg1bs && opn in p.msg.votes && LValIsHighestNumberedProposalAtBallot(v, p.msg.votes[opn].max_value_bal, msg1bs, opn))
{
  var c :| CountInVotes(v, c, opn, msg1bs) >= wq && AllVotesWithLargerBalHasSameValue(v, c, msg1bs, opn);
  assert forall p :: p in msg1bs && opn in p.msg.votes && BalLeq(c, p.msg.votes[opn].max_value_bal) ==> p.msg.votes[opn].max_val == v;
  // assert exists p :: p in msg1bs && opn in p.votes && Lmax_balInS(p.votes[opn].max_value_bal, msg1bs, opn);
  // var p :| p in msg1bs && opn in p.votes && Lmax_balInS(p.votes[opn].max_value_bal, msg1bs, opn);

  var p :| p in msg1bs && opn in p.msg.votes;
  assert p.msg.RslMessage_1b?;
  var i := 0;
  while i < |msg1bs|
    invariant 0 <= i <= |msg1bs|
    invariant p.msg.RslMessage_1b?
    invariant p in msg1bs
    invariant opn in p.msg.votes
    invariant forall j :: 0 <= j < i && opn in msg1bs[j].msg.votes ==> BalLeq(msg1bs[j].msg.votes[opn].max_value_bal, p.msg.votes[opn].max_value_bal)
    invariant Lmax_balInS(p.msg.votes[opn].max_value_bal, msg1bs[..i], opn)
    // decreases |msg1bs| - i
  {
    assert forall j :: 0 <= j < i && opn in msg1bs[j].msg.votes && opn in p.msg.votes ==> BalLeq(msg1bs[j].msg.votes[opn].max_value_bal, p.msg.votes[opn].max_value_bal);
    if opn in msg1bs[i].msg.votes && opn !in p.msg.votes {
      p := msg1bs[i];
      assert BalLeq(msg1bs[i].msg.votes[opn].max_value_bal, p.msg.votes[opn].max_value_bal);
      assert forall j :: 0 <= j <= i && opn in msg1bs[j].msg.votes && opn in p.msg.votes ==> BalLeq(msg1bs[j].msg.votes[opn].max_value_bal, p.msg.votes[opn].max_value_bal);
    }
    else if opn in msg1bs[i].msg.votes && opn in p.msg.votes && BalLeq(p.msg.votes[opn].max_value_bal, msg1bs[i].msg.votes[opn].max_value_bal)
    {
      p := msg1bs[i];
    }
    else
    {
      p := p;
    }
    i := i + 1;
  }
  assert p in msg1bs;
  assert opn in p.msg.votes;

  // var i := 0;
  // var j := 0;
  // while i < |msg1bs|
  //   invariant 0 <= j <= i <= |msg1bs|
  //   // decreases |msg1bs| - i
  // {
  //   var pi := msg1bs[i];
  //   var pj := msg1bs[j];
  //   if opn in pi.votes && opn !in pj.votes {
  //     j := i;
  //   }
  //   else if opn in pi.votes && opn in pj.votes && BalLeq(pj.votes[opn].max_value_bal, pi.votes[opn].max_value_bal)
  //   {
  //     j := i;
  //   }
  //   else
  //   {
  //     j := j;
  //   }
  //   i := i + 1;
  // }

  assert CountInVotes(v, c, opn, msg1bs) >= wq;
  assert wq > 0;
  assert exists q :: q in msg1bs && opn in q.msg.votes && BalLeq(c, q.msg.votes[opn].max_value_bal);

  // var p := msg1bs[0];
  // assert opn in p.votes;
  assert forall q :: q in msg1bs && opn in q.msg.votes ==> BalLeq(q.msg.votes[opn].max_value_bal, p.msg.votes[opn].max_value_bal);
  // assert exists q :: q in msg1bs && opn in q.votes && q.votes[opn].max_value_bal==c;
  assert BalLeq(c, p.msg.votes[opn].max_value_bal);
  assert forall m :: m in msg1bs && opn in m.msg.votes && BalLeq(c, m.msg.votes[opn].max_value_bal) ==> m.msg.votes[opn].max_val == v;
  assert p in msg1bs && opn in p.msg.votes && BalLeq(c, p.msg.votes[opn].max_value_bal);
  assert p.msg.votes[opn].max_val == v;
}
/**
验证目标：一个q2bs的val和一个bal更大的1c的val一样

q2avs2 -> packet1c_overlap
2b -> packet2b_overlap
1b -> packet1b_overlap

q2av -> packet1c
1b2 -> chosen_packet1b
q2av3 -> previous_packet1c （从1b2推出来，是之前bal发的1c）

步骤：
2. 找到1c对应的1b set
3. 找到1b set和q2bs的交集节点
4. 找到这个交集发出的 2b 和 1b，2b 应该是早于1b的
5. 找到决定2a val的那个1b （1b2）
6. 找到1b2 对应的 q2avs3 和 1c3，也就是导致这次投票的1c
7. 如果q2bs 和 1c3 的bal一样，说明在这个bal达成共识的
   此时找到2b对应的 1c2，证明1c2 和 1c3的val一样
8. 如果q2bs的bal和1c3的bal不一样，证明达成共识的bal还要更早
   通过1c3为输入，递归往前匹配
 */
lemma lemma_ChosenQuorumAnd1cFromLaterBallotMatchValues(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  quorum_of_2bs:QuorumOf2bs,
  packet1c:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires IsValidQuorumOf2bs(b[i], quorum_of_2bs)
  // requires IsValidQuorumOf2avs(b[i], q2av)
  requires packet1c in b[i].environment.sentPackets
  requires packet1c.src in c.config.replica_ids
  requires packet1c.msg.RslMessage_1c?
  requires quorum_of_2bs.opn == packet1c.msg.opn_1c
  requires BalLt(quorum_of_2bs.bal, packet1c.msg.bal_1c)
  ensures  quorum_of_2bs.v == packet1c.msg.val_1c
  decreases packet1c.msg.bal_1c.seqno, packet1c.msg.bal_1c.proposer_id
{
  lemma_ConstantsAllConsistent(b, c, i);

  var opn := quorum_of_2bs.opn;

  // var idx :| idx in q2av.indices;
  // var p2av := q2av.packets[idx];
  // var p1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i, p2av);
  var q1bs := lemma_1cMessageHas1bQuorumPermittingIt(b, c, i, packet1c);
  // assert p2av.msg.val_2av == p1c.msg.val_1c;

  var q1bmsgs := Convert1bPacketsSeqToMsgSeq(q1bs);
  lemma_Convert1bPacketsSeqToMsgSeqIsConsistent(q1bs, q1bmsgs);
  assert forall i :: 0 <= i < |q1bs| ==> q1bmsgs[i] == q1bs[i].msg;
  assert |q1bs| >= LByzQuorumSize(c.config);
  var quorum_of_1bs := ConvertSeqToSet(q1bs);
  lemma_SeqToSetLengthNotChange(q1bs);
  assert |quorum_of_1bs| >= LByzQuorumSize(c.config);
  // // var quorum_of_1bs := lemma_2aMessageHas1bQuorumPermittingIt(b, c, i, packet2a);
  var quorum_of_1bs_indices := lemma_GetIndicesFromPackets(quorum_of_1bs, c.config);
  assert |quorum_of_1bs_indices| >= LByzQuorumSize(c.config);
  assert |quorum_of_2bs.indices| >= LMinQuorumSize(c.config);

  var overlap_idx := lemma_QuorumIndexOverlap(quorum_of_1bs_indices, quorum_of_2bs.indices, |c.config.replica_ids|);
  var packet1b_overlap :| packet1b_overlap in q1bs && packet1b_overlap.src == c.config.replica_ids[overlap_idx];
  var packet2b_overlap := quorum_of_2bs.packets[overlap_idx];

  var byzq := LByzQuorumSize(c.config);
  var wq := LMinQuorumSize(c.config);
  assert wq > 0;

  if opn !in packet1b_overlap.msg.votes
  {
    // assert BalLt(packet2b_overlap.msg.bal_2b, packet1b_overlap.msg.bal_1b);
    lemma_1bMessageWithoutOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);
    assert false;
  }
  // assert opn in packet1b_overlap.msg.votes;

  var val := packet1c.msg.val_1c;
  assert LValIsSafeAt(val, q1bs, opn, byzq, wq);
  lemma_LValIsSafeAtImpliesLValIsHighestNumberedProposalAtBallot(val, q1bs, opn, byzq, wq);
  assert exists p :: p in q1bs && opn in p.msg.votes && LValIsHighestNumberedProposalAtBallot(val, p.msg.votes[opn].max_value_bal, q1bs, opn);
  // assert exists p :: p in q1bs && opn in p.msg.votes && p.msg.votes[opn].max_val == val;

  var p :| p in q1bmsgs && opn in p.votes && LValIsHighestNumberedProposalAtBallot(val, p.votes[opn].max_value_bal, q1bs, opn);
  assert p.RslMessage_1b?;
  var highestballot_in_1b_set := p.votes[opn].max_value_bal;
  assert LValIsHighestNumberedProposalAtBallot(val, highestballot_in_1b_set, q1bs, opn);
  // var highestballot_in_1b_set :| 
  //   LValIsHighestNumberedProposalAtBallot(val, highestballot_in_1b_set, q1bmsgs, opn);
  // assert BalLeq(packet1b_overlap.msg.votes[opn].max_value_bal, highestballot_in_1b_set);
  var packet1b_highestballot :| && packet1b_highestballot in q1bs
                                && opn in packet1b_highestballot.msg.votes
                                && packet1b_highestballot.msg.votes[opn] == Vote(highestballot_in_1b_set, val);

  // var chosen_packet1b :| 
  //     && chosen_packet1b in q1bs
  //     && opn in chosen_packet1b.msg.votes
  //     && chosen_packet1b.msg.votes[opn].max_val == val;
  //     // && LValIsSafeAt(val, q1bmsgs, opn, byzq, wq);
  // assert chosen_packet1b.msg.votes[opn].max_val == val;

  // assert BalLeq(chosen_packet1b.msg.votes[opn].max_value_bal, packet1b_highestballot.msg.votes[opn].max_value_bal);
  // // assert chosen_packet1b.msg.votes[opn].max_val == packet1b_highestballot.msg.votes[opn].max_val;

  assert BalLeq(quorum_of_2bs.bal, packet1b_highestballot.msg.bal_1b);
  assert BalLeq(packet1b_overlap.msg.votes[opn].max_value_bal, highestballot_in_1b_set);
  lemma_Vote1bMessageIsFromEarlierBallot(b, c, i, opn, packet1b_highestballot);

  lemma_1bMessageWithOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);

  assert BalLeq(packet2b_overlap.msg.bal_2b, packet1b_overlap.msg.bal_1b);
  assert quorum_of_2bs.bal == packet2b_overlap.msg.bal_2b;

  assert BalLeq(quorum_of_2bs.bal, packet1b_highestballot.msg.votes[opn].max_value_bal);

  var previous_packet1c := lemma_1bMessageWithOpnImplies1cSent(b, c, i, opn, packet1b_highestballot);
  assert previous_packet1c.msg.bal_1c == packet1b_highestballot.msg.votes[opn].max_value_bal;
  assert previous_packet1c.msg.val_1c == packet1b_highestballot.msg.votes[opn].max_val;
  assert BalLt(previous_packet1c.msg.bal_1c, packet1c.msg.bal_1c);

  if quorum_of_2bs.bal == previous_packet1c.msg.bal_1c
  {
    var q2av_overlap := lemma_2bSentIsAllowed(b, c, i, packet2b_overlap);
    var idx2 :| idx2 in q2av_overlap.indices;
    var packet2av_overlap := q2av_overlap.packets[idx2];
    var packet1c_overlap := lemma_2avMessageHasCorresponding1cMessage(b, c, i, packet2av_overlap);
    lemma_1cMessagesFromSameBallotAndOperationMatch(b, c, i, packet1c_overlap, previous_packet1c);
    assert quorum_of_2bs.v == previous_packet1c.msg.val_1c;
    assert previous_packet1c.msg.val_1c == packet1c.msg.val_1c;
    assert quorum_of_2bs.v == packet1c.msg.val_1c;
  }
  else
  {
    lemma_1cMessageHasValidBallot(b, c, i, packet1c);
    assert BalLt(quorum_of_2bs.bal, previous_packet1c.msg.bal_1c);
    lemma_ChosenQuorumAnd1cFromLaterBallotMatchValues(b, c, i, quorum_of_2bs, previous_packet1c);
    assert quorum_of_2bs.v == previous_packet1c.msg.val_1c;
    assert previous_packet1c.msg.val_1c == packet1c.msg.val_1c;
    assert quorum_of_2bs.v == packet1c.msg.val_1c;
  }

  // assert BalLeq(quorum_of_2bs.bal, chosen_packet1b.msg.votes[opn].max_value_bal);
  // // assert BalLeq(packet1b_overlap.msg.votes[opn].max_value_bal, chosen_packet1b.msg.votes[opn].max_value_bal);
  // lemma_Vote1bMessageIsFromEarlierBallot(b, c, i, opn, chosen_packet1b);

  // lemma_1bMessageWithOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);

  // var previous_packet1c := lemma_1bMessageWithOpnImplies1cSent(b, c, i, opn, chosen_packet1b);
  // assert previous_packet1c.msg.bal_1c == chosen_packet1b.msg.votes[opn].max_value_bal;
  // assert previous_packet1c.msg.val_1c == chosen_packet1b.msg.votes[opn].max_val;
  // assert BalLt(previous_packet1c.msg.bal_1c, packet1c.msg.bal_1c);

  // if quorum_of_2bs.bal == previous_packet1c.msg.bal_1c
  // {
  //   var q2av_overlap := lemma_2bSentIsAllowed(b, c, i, packet2b_overlap);
  //   var idx2 :| idx2 in q2av_overlap.indices;
  //   var packet2av_overlap := q2av_overlap.packets[idx2];
  //   var packet1c_overlap := lemma_2avMessageHasCorresponding1cMessage(b, c, i, packet2av_overlap);
  //   lemma_1cMessagesFromSameBallotAndOperationMatch(b, c, i, packet1c_overlap, previous_packet1c);
  //   assert quorum_of_2bs.v == previous_packet1c.msg.val_1c;
  //   assert previous_packet1c.msg.val_1c == packet1c.msg.val_1c;
  //   assert quorum_of_2bs.v == packet1c.msg.val_1c;
  // }
  // else
  // {
  //   lemma_1cMessageHasValidBallot(b, c, i, packet1c);
  //   assert BalLt(quorum_of_2bs.bal, previous_packet1c.msg.bal_1c);
  //   lemma_ChosenQuorumAnd1cFromLaterBallotMatchValues(b, c, i, quorum_of_2bs, previous_packet1c);
  //   assert quorum_of_2bs.v == previous_packet1c.msg.val_1c;
  //   assert previous_packet1c.msg.val_1c == packet1c.msg.val_1c;
  //   assert quorum_of_2bs.v == packet1c.msg.val_1c;
  // }

}


lemma lemma_ChosenQuorumsMatchValue(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  q1:QuorumOf2bs,
  q2:QuorumOf2bs
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires IsValidQuorumOf2bs(b[i], q1)
  requires IsValidQuorumOf2bs(b[i], q2)
  requires q1.opn == q2.opn
  ensures  q1.v == q2.v
{
  lemma_ConstantsAllConsistent(b, c, i);

  var idx1 :| idx1 in q1.indices;
  var idx2 :| idx2 in q2.indices;
  var p1_2b := q1.packets[idx1];
  var p2_2b := q2.packets[idx2];
  // var p1_2a := lemma_2bMessageHasCorresponding2aMessage(b, c, i, p1_2b);
  // var p2_2a := lemma_2bMessageHasCorresponding2aMessage(b, c, i, p2_2b);

  var q1_2av := lemma_2bSentIsAllowed(b, c, i, p1_2b);
  var q2_2av := lemma_2bSentIsAllowed(b, c, i, p2_2b);

  assert q1_2av.bal == p1_2b.msg.bal_2b;
  assert q2_2av.bal == p2_2b.msg.bal_2b;

  var idx3 :| idx3 in q1_2av.indices;
  var idx4 :| idx4 in q2_2av.indices;
  var p1_2av := q1_2av.packets[idx3];
  var p2_2av := q2_2av.packets[idx4];

  var p1_1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i, p1_2av);
  var p2_1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i, p2_2av);
  
  if q1.bal == q2.bal
  {
    // lemma_2avMessagesFromSameBallotAndOperationMatch(b, c, i, p1_2av, p2_2av);
    lemma_1cMessagesFromSameBallotAndOperationMatch(b, c, i, p1_1c, p2_1c);
  }
  else if BalLt(q1.bal, q2.bal)
  {
    lemma_ChosenQuorumAnd1cFromLaterBallotMatchValues(b, c, i, q1, p2_1c);
  }
  else
  {
    lemma_ChosenQuorumAnd1cFromLaterBallotMatchValues(b, c, i, q2, p1_1c);
  }
}

lemma lemma_CountMatchesInSeqOfDiffValNotExceedTheSeqSize(s:seq<RequestBatch>, v1:RequestBatch, v2:RequestBatch)
  requires v1 != v2
  ensures CountMatchesInSeq(s, x => x == v1) + CountMatchesInSeq(s, x => x == v2) <= |s|
{
  var c1 := CountMatchesInSeq(s, x => x == v1);
  var c2 := CountMatchesInSeq(s, x => x == v2);

  if |s| == 0 {
    assert c1 == 0;
    assert c2 == 0;
    assert c1 + c2 <= |s|;
  } else {
    var tail := s[1..];
    lemma_CountMatchesInSeqOfDiffValNotExceedTheSeqSize(tail, v1, v2);
  }
}

lemma lemma_CountMatchedValInReceived2bsOfDiffValNotExceedTheSeqSize(s:seq<RslPacket>, v1:RequestBatch, v2:RequestBatch)
  requires v1 != v2
  requires forall p :: p in s ==> p.msg.RslMessage_2b?
  ensures CountMatchedValInReceived2bs(s, v1) + CountMatchedValInReceived2bs(s, v2) <= |s|
{
  var c1 := CountMatchedValInReceived2bs(s, v1);
  var c2 := CountMatchedValInReceived2bs(s, v2);

  if |s| == 0 {
    assert c1 == 0;
    assert c2 == 0;
    assert c1 + c2 <= |s|;
  } else {
    var tail := s[..|s|-1];
    lemma_CountMatchedValInReceived2bsOfDiffValNotExceedTheSeqSize(tail, v1, v2);
    assert CountMatchedValInReceived2bs(tail, v1) + CountMatchedValInReceived2bs(tail, v2) <= |tail|;
    assert |s| == |tail| + 1;
    // if s[0].msg.val_2b  == v1 {
    //   assert CountMatchedValInReceived2bs(s, v1) == CountMatchedValInReceived2bs(tail, v1) + 1;
    //   assert CountMatchedValInReceived2bs(tail, v2) == CountMatchedValInReceived2bs(tail, v2);
    //   assert CountMatchedValInReceived2bs(s, v1) + CountMatchedValInReceived2bs(tail, v2) <= |s|;
    // }
    assert CountMatchedValInReceived2bs(s, v1) + CountMatchedValInReceived2bs(tail, v2) <= |s|;
  }
}

lemma lemma_ChoseExecuteValFromMinQuorumIsUnique(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int,
  v1:RequestBatch,
  v2:RequestBatch
)
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires var s := b[i].replicas[idx].replica;
            s.executor.ops_complete in s.learner.unexecuted_learner_state     
  requires var s := b[i].replicas[idx].replica;
           var opn := s.executor.ops_complete;
           && LearnerStateCorrect(s.learner.unexecuted_learner_state, s.learner.max_ballot_seen, s.learner.constants.all.config)
            && CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, v1) >= LMinQuorumSize(s.constants.all.config)
  requires var s := b[i].replicas[idx].replica;
           var opn := s.executor.ops_complete;
            && CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, v2) >= LMinQuorumSize(s.constants.all.config)
  ensures v1 == v2
{
  var s := b[i].replicas[idx].replica;
  var opn := s.executor.ops_complete;
  var quorum := LMinQuorumSize(s.constants.all.config);
  Lemma_TwoMinQuorumsIntersect(s.constants.all.config);
  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  assert quorum + quorum > |s.constants.all.config.replica_ids|;
  assert |s.learner.unexecuted_learner_state[opn].received_2bs| <= |s.learner.constants.all.config.replica_ids|;
  if v1 != v2 
  {
    var c1 := CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, v1);
    var c2 := CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, v2);
    assert c1 >= quorum;
    assert c2 >= quorum;
    assert c1 + c2 > |s.constants.all.config.replica_ids|;
    lemma_CountMatchedValInReceived2bsOfDiffValNotExceedTheSeqSize(s.learner.unexecuted_learner_state[opn].received_2bs, v1, v2);
    assert c1 + c2 <= |s.learner.unexecuted_learner_state[opn].received_2bs|;
    assert false;
  }
}

lemma {:opaque} lemma_DecidedOperationWasChosen(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int
  ) returns (
  q:QuorumOf2bs
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires b[i].replicas[idx].replica.executor.next_op_to_execute.OutstandingOpKnown?
  ensures  IsValidQuorumOf2bs(b[i], q)
  ensures  var s := b[i].replicas[idx].replica.executor;
           q.bal == s.next_op_to_execute.bal && q.opn == s.ops_complete && q.v == s.next_op_to_execute.v
{
  if i == 0
  {
    return;
  }

  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var s := b[i-1].replicas[idx].replica;
  var s' := b[i].replicas[idx].replica;

  if s'.executor.next_op_to_execute == s.executor.next_op_to_execute
  {
    q := lemma_DecidedOperationWasChosen(b, c, i-1, idx);
    lemma_QuorumOf2bsStaysValid(b, c, i-1, i, q);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  assert b[i-1].replicas[idx].nextActionIndex == 7;
  var opn := s.executor.ops_complete;
  var bal := s.learner.max_ballot_seen;

  var pkt :| pkt in s.learner.unexecuted_learner_state[opn].received_2bs
                && CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, pkt.msg.val_2b) >= LMinQuorumSize(s.constants.all.config);
  var v := pkt.msg.val_2b;
  var v2 := s'.executor.next_op_to_execute.v;
  var pkt2 :| pkt2 in s.learner.unexecuted_learner_state[opn].received_2bs && pkt2.msg.val_2b == v2;
  assert CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, v) >= LMinQuorumSize(s.constants.all.config);
  assert CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, v2) >= LMinQuorumSize(s.constants.all.config);
  lemma_ChoseExecuteValFromMinQuorumIsUnique(b, c, i, idx, v, v2);
  assert v == s'.executor.next_op_to_execute.v;

  var p2bs := s.learner.unexecuted_learner_state[opn].received_2bs;
  // var cvals := s.learner.unexecuted_learner_state[opn].candidate_learned_value;
  var indices:set<int> := {};
  var srcs:set<NodeIdentity> := {};
  
  var sender_idx := 0;
  var dummy_packet := LPacket(c.config.replica_ids[0], c.config.replica_ids[0], RslMessage_2b(Ballot(0, 0), 0, []));
  var packets:seq<RslPacket> := seq(|c.config.replica_ids|, idx => dummy_packet);
  assert |packets| == |c.config.replica_ids|;
  assert forall p :: p in packets ==> p.msg.RslMessage_2b?;

  assert LearnerStateCorrect(s.learner.unexecuted_learner_state, s.learner.max_ballot_seen, s.learner.constants.all.config);
  // assert |p2bs| == |cvals|;
  assert (forall p :: p in p2bs ==> p.msg.RslMessage_2b?);
  assert (forall p :: p in p2bs ==> p.msg.opn_2b == opn);
  // assert (forall p :: p in p2bs ==> p.msg.bal_2b == bal);
  // assert (forall i :: 0 <= i < |p2bs| ==> p2bs[i].msg.val_2b == cvals[i]);
  assert (forall i,j :: 0 <= i < |p2bs| && 0 <= j < |p2bs| && i != j 
                  ==> p2bs[i] != p2bs[j] && p2bs[i].src != p2bs[j].src);

  var count := 0;
  var temp_pkts:seq<RslPacket> := [];
  assert CountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, v) >= LMinQuorumSize(s.constants.all.config);

  var iter := 0;
  while iter < |p2bs|
    invariant 0 <= iter <= |p2bs|
    invariant |temp_pkts| == iter
    invariant temp_pkts == p2bs[..iter]
    invariant forall pkt :: pkt in temp_pkts ==> pkt.msg.RslMessage_2b?
    invariant forall iidx :: 0 <= iidx < iter && p2bs[iidx].msg.val_2b == v
                     ==> p2bs[iidx].src in srcs && GetReplicaIndex(p2bs[iidx].src, c.config) in indices
    invariant forall src :: src in srcs ==> src in c.config.replica_ids && GetReplicaIndex(src, c.config) in indices
    invariant forall j :: iter <= j < |p2bs| ==> (forall src :: src in srcs ==> p2bs[j].src != src)
    invariant forall j :: iter <= j < |p2bs| ==> (forall iidx :: iidx in indices ==> GetReplicaIndex(p2bs[j].src, c.config) != iidx)
    invariant count == CountMatchedValInReceived2bs(temp_pkts, v)
    invariant count == |srcs| == |indices|
    invariant |packets| == |c.config.replica_ids|
    invariant forall sidx :: sidx in indices ==> 
                && 0 <= sidx < |c.config.replica_ids|
                && var p := packets[sidx];
                && p.src == b[i].constants.config.replica_ids[sidx]
                && p.msg.RslMessage_2b?
                && p.msg.opn_2b == opn
                && p.msg.val_2b == v
                && p.msg.bal_2b == bal
                && p in b[i].environment.sentPackets
  {
    var p := p2bs[iter];
    assert count == CountMatchedValInReceived2bs(temp_pkts, v);
    lemma_CountMatchedValInReceived2bs_append_one(p2bs, v, iter);
  
    var index := GetReplicaIndex(p.src, c.config);
    if p.msg.val_2b == v {
      assert 0 <= index < |c.config.replica_ids|;
      assert |packets| == |c.config.replica_ids|;

      lemma_PacketInReceived2bWasSent(b, c, i, idx, opn, p);
      packets := packets[index := p];
     
      assert forall src :: src in srcs ==> p.src != src;
     
      assert forall iidx :: iidx in indices ==> index != iidx;
      
      var new_srcs := srcs;
      var new_indices := indices;
      new_srcs := new_srcs + {p.src};
      new_indices := indices + {index};
      srcs := new_srcs;
      indices := new_indices;
      
      temp_pkts := temp_pkts + [p];
      count := count + 1;
      assert temp_pkts == p2bs[..iter+1];
      assert count == CountMatchedValInReceived2bs(p2bs[..iter], v) + 1;
      assert count == CountMatchedValInReceived2bs(p2bs[..iter+1], v);
      assert 0 <= index < |c.config.replica_ids|;
      assert p == packets[index];
      assert p.msg.RslMessage_2b?;
      assert p.msg.opn_2b == opn;
      assert p.msg.val_2b == v;
      assert p.msg.bal_2b == bal;
      assert p in b[i].environment.sentPackets;
    }
    else 
    {
      assert 0 <= index < |c.config.replica_ids|;
      assert |packets| == |c.config.replica_ids|;
      packets := packets[index := p];
      temp_pkts := temp_pkts + [p];
      assert count == CountMatchedValInReceived2bs(p2bs[..iter], v);
      assert count == CountMatchedValInReceived2bs(p2bs[..iter+1], v);
    }
    iter := iter + 1;
  }
  assert temp_pkts == p2bs;
  assert |srcs| >= LMinQuorumSize(s'.constants.all.config);
  assert |indices| >= LMinQuorumSize(s'.constants.all.config);
  q := QuorumOf2bs(c, indices, packets, bal, opn, v);
}

lemma lemma_CountMatchedValInReceived2bs_append_one(s: seq<RslPacket>, v: RequestBatch, i: int)
  requires 0 <= i < |s|
  requires forall p :: p in s ==> p.msg.RslMessage_2b?
  ensures CountMatchedValInReceived2bs(s[..i+1], v) == CountMatchedValInReceived2bs(s[..i], v) + (if s[i].msg.val_2b == v then 1 else 0)
{
  if i == 0 {
    assert s[..i+1] == [s[0]];
    assert CountMatchedValInReceived2bs(s[..i+1], v) == (if s[0].msg.val_2b == v then 1 else 0);
    assert CountMatchedValInReceived2bs(s[..i], v) == 0;
  } else {
    assert s[..i+1] == s[..i] + [s[i]]; 
    assert CountMatchedValInReceived2bs(s[..i+1], v) == CountMatchedValInReceived2bs(s[..i],v) + if v == s[i].msg.val_2b then 1 else 0;
  }
}

// lemma lemma_ExecutedOperationAndAllBeforeItWereChosen(
//   b:Behavior<RslState>,
//   c:LConstants,
//   i:int,
//   idx:int
//   ) returns (
//   qs:seq<QuorumOf2bs>
//   )
//   requires IsValidBehaviorPrefix(b, c, i)
//   requires 0 <= i
//   requires 0 <= idx < |b[i].replicas|
//   ensures  |qs| == b[i].replicas[idx].replica.executor.ops_complete
//   ensures  forall opn :: 0 <= opn < |qs| ==> && IsValidQuorumOf2bs(b[i], qs[opn])
//                                       && qs[opn].opn == opn
//                                       && BalLeq(qs[opn].bal, b[i].replicas[idx].replica.executor.max_bal_reflected)
//   decreases i
// {
//   if i == 0
//   {
//     qs := [];
//     return;
//   }

//   lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
//   lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
//   lemma_AssumptionsMakeValidTransition(b, c, i-1);

//   var s := b[i-1].replicas[idx].replica.executor;
//   var s' := b[i].replicas[idx].replica.executor;

//   if s'.ops_complete == s.ops_complete
//   {
//     qs := lemma_ExecutedOperationAndAllBeforeItWereChosen(b, c, i-1, idx);
//     forall opn | 0 <= opn < |qs|
//       ensures IsValidQuorumOf2bs(b[i], qs[opn])
//     {
//       lemma_QuorumOf2bsStaysValid(b, c, i-1, i, qs[opn]);
//     }
//     if s'.max_bal_reflected != s.max_bal_reflected
//     {
//       var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
//       assert false;
//     }
//     return;
//   }

//   var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
//   if b[i-1].replicas[idx].nextActionIndex == 0
//   {
//     var p := ios[0].r;
//     qs := lemma_TransferredStateBasedOnChosenOperations(b, c, i-1, p);
//     return;
//   }

//   var prev_qs := lemma_ExecutedOperationAndAllBeforeItWereChosen(b, c, i-1, idx);
//   var q := lemma_DecidedOperationWasChosen(b, c, i-1, idx);
//   qs := prev_qs + [q];
// }

// lemma lemma_TransferredStateBasedOnChosenOperations(
//   b:Behavior<RslState>,
//   c:LConstants,
//   i:int,
//   p:RslPacket
//   ) returns (
//   qs:seq<QuorumOf2bs>
//   )
//   requires IsValidBehaviorPrefix(b, c, i)
//   requires 0 <= i
//   requires p in b[i].environment.sentPackets
//   requires p.src in c.config.replica_ids
//   requires p.msg.RslMessage_AppStateSupply?
//   ensures  |qs| == p.msg.opn_state_supply
//   ensures  forall opn :: 0 <= opn < |qs| ==> && IsValidQuorumOf2bs(b[i], qs[opn])
//                                       && qs[opn].opn == opn
//                                       && BalLeq(qs[opn].bal, p.msg.bal_state_supply)
//   decreases i
// {
//   if i == 0
//   {
//     return;
//   }

//   lemma_ConstantsAllConsistent(b, c, i-1);
//   lemma_ConstantsAllConsistent(b, c, i);

//   if p in b[i-1].environment.sentPackets
//   {
//     qs := lemma_TransferredStateBasedOnChosenOperations(b, c, i-1, p);
//     forall opn | 0 <= opn < |qs|
//       ensures IsValidQuorumOf2bs(b[i], qs[opn])
//     {
//       lemma_QuorumOf2bsStaysValid(b, c, i-1, i, qs[opn]);
//     }
//     return;
//   }

//   lemma_AssumptionsMakeValidTransition(b, c, i-1);
//   var idx, ios := lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(b[i-1], b[i], p);
//   qs := lemma_ExecutedOperationAndAllBeforeItWereChosen(b, c, i-1, idx);
// }

}
