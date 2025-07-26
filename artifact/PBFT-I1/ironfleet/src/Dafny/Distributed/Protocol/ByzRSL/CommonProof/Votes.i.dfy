include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "Quorum.i.dfy"
include "Message1c.i.dfy"
include "Message2av.i.dfy"
include "Message2b.i.dfy"

module CommonProof__Votes_i{
import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Types_i
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Acceptor_i
import opened LiveByzRSL__Replica_i
import opened LiveByzRSL__Message_i
// import opened CommonProof__AcceptorState_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Constants_i
import opened CommonProof__Actions_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Environment_i
// import opened CommonProof__QuorumOf2avs_i
import opened CommonProof__Quorum_i
// import opened CommonProof__Received2av_i
import opened CommonProof__Message1c_i
import opened CommonProof__Message2av_i
import opened CommonProof__Message2b_i
import opened Concrete_NodeIdentity_i
import opened Temporal__Temporal_s
import opened Environment_s
import opened Collections__CountMatches_i
import opened Collections__Sets_i


/**
opn 在 s 和 s' 的votes都存在
且bal相同，
证明：val也相同
*/
lemma lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    opn:OperationNumber,
    bal:Ballot,
    idx:int
)
    requires IsValidBehaviorPrefix(b, c, i+1)
    requires 0 <= i
    requires 0 <= idx < |b[i].replicas|
    requires 0 <= idx < |b[i+1].replicas|
    requires opn in b[i].replicas[idx].replica.acceptor.votes
    requires opn in b[i+1].replicas[idx].replica.acceptor.votes
    requires b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_value_bal
    ensures  b[i].replicas[idx].replica.acceptor.votes[opn].max_val == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_val
{
    lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
    lemma_ReplicaConstantsAllConsistent(b, c, i+1, idx);
    lemma_AssumptionsMakeValidTransition(b, c, i);

    var s := b[i].replicas[idx].replica.acceptor;
    var s' := b[i+1].replicas[idx].replica.acceptor;

    if s'.votes[opn].max_val != s.votes[opn].max_val
    {
        var nextActionIndex := b[i].replicas[idx].nextActionIndex;
        assert nextActionIndex == 0 || nextActionIndex == 5;
        
        if nextActionIndex == 0 {
          var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i, idx);
          var earlier_1c := lemma_Find1cThatCausedVote(b, c, i, idx, opn);
          lemma_1cMessagesFromSameBallotAndOperationMatch(b, c, i+1, earlier_1c, ios[0].r);
          assert false;
        }
        else 
        {
          var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i, idx);
          var earlier_1c := lemma_Find1cThatCausedVote(b, c, i, idx, opn);
          var packets := ExtractSentPacketsFromIos(ios);
          var p_2b := packets[0];
          var vbal := s.val_to_be_sent_2b.bal;
          var vval := s.val_to_be_sent_2b.v;
          assert p_2b.msg.RslMessage_2b?;
          assert p_2b.msg.bal_2b == vbal;
          assert p_2b.msg.val_2b == vval;
          var q2avs := lemma_2bSentIsMaybeSend2b(b, c, i, p_2b, idx, ios);
          var idx2 :| idx2 in q2avs.indices;
          var p_2av := q2avs.packets[idx2];

          var p_1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i+1, p_2av);
          lemma_1cMessagesFromSameBallotAndOperationMatch(b, c, i+1, earlier_1c, p_1c);
        }
    }
}

/**
acceptor s发出了2b消息
证明目标：
2b.opn 在 s 的votes里
2b.bal <= s.votes[opn].max_val_bal，为什么是<=呢？？？
如果2b.bal == s.votes[opn].max_val_bal，那么2b.val == s.votes[opn].max_val
 */
lemma lemma_2bMessageImplicationsForCAcceptor(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p:RslPacket
) returns (
    acceptor_idx:int
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p in b[i].environment.sentPackets
  requires p.src in c.config.replica_ids
  requires p.msg.RslMessage_2b?
  ensures  0 <= acceptor_idx < |c.config.replica_ids|
  ensures  0 <= acceptor_idx < |b[i].replicas|
  ensures  p.src == c.config.replica_ids[acceptor_idx]
  ensures  BalLeq(p.msg.bal_2b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal)
  ensures  var s := b[i].replicas[acceptor_idx].replica.acceptor;
           p.msg.opn_2b >= s.log_truncation_point ==>
              p.msg.opn_2b in s.votes
              && BalLeq(p.msg.bal_2b, s.votes[p.msg.opn_2b].max_value_bal)
              && (s.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s.votes[p.msg.opn_2b].max_val == p.msg.val_2b)
  decreases i
{
  if i == 0
  {
    return;
  }

  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_ConstantsAllConsistent(b, c, i-1);

  var v := p.msg.val_2b;
  var opn := p.msg.opn_2b;
  var bal := p.msg.bal_2b;

  if p in b[i-1].environment.sentPackets
  {
    acceptor_idx := lemma_2bMessageImplicationsForCAcceptor(b, c, i-1, p);
    var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
    var s' := b[i].replicas[acceptor_idx].replica.acceptor;

    // var nextIndex := b[i-1].replicas[acceptor_idx].nextActionIndex;
    // assert nextIndex == 
    // assert p.msg.opn_2b in s.votes;
    // assert BalLeq(p.msg.bal_2b, s.votes[p.msg.opn_2b].max_value_bal);
    // assert (s.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s.votes[p.msg.opn_2b].max_val == p.msg.val_2b);

    if s' != s
    {
      // var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, acceptor_idx);
      if opn >= s'.log_truncation_point
      {
        assert p.msg.opn_2b in s'.votes;
        lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, acceptor_idx);
        if s'.votes[opn].max_value_bal == s.votes[opn].max_value_bal
        {
          lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, bal, acceptor_idx);
        }
        assert p.msg.opn_2b in s'.votes;
        assert BalLeq(p.msg.bal_2b, s'.votes[p.msg.opn_2b].max_value_bal);
        assert (s'.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s'.votes[p.msg.opn_2b].max_val == p.msg.val_2b);
      }
    }
    assert p.msg.opn_2b >= s'.log_truncation_point ==>
              p.msg.opn_2b in s'.votes
              && BalLeq(p.msg.bal_2b, s'.votes[p.msg.opn_2b].max_value_bal)
              && (s'.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s'.votes[p.msg.opn_2b].max_val == p.msg.val_2b);
    return;
  }

  
  var ios:seq<RslIo>;
  acceptor_idx, ios := lemma_ActionThatSends2bIsMaybeSend2b(b[i-1], b[i], p);

  // var q2avs := lemma_2bSentIsAllowed(b, c, i, p);
  // assert acceptor_idx in q2avs.indices;
  // var p2av := q2avs.packets[acceptor_idx];
  // var p1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i, p2av);
  
  var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
  var s' := b[i].replicas[acceptor_idx].replica.acceptor;
  var vbal := s.val_to_be_sent_2b.bal;
  var vval := s.val_to_be_sent_2b.v;
  assert p.msg.bal_2b == vbal == s.max_bal == s'.max_bal;
  assert p.msg.val_2b == vval;
  assert p.msg.bal_2b == s'.max_bal;
  // if p.msg.opn_2b >= s'.log_truncation_point 
  // {
  //   if opn !in s.votes {
  //     assert s'.votes[p.msg.opn_2b].max_value_bal == bal;
  //     assert s'.votes[p.msg.opn_2b].max_val == vval;
  //   }
  //   else 
  //   {
  //     // if 
  //   }
  // }
  assert p.msg.opn_2b >= s'.log_truncation_point ==>
              p.msg.opn_2b in s'.votes
              // && s'.votes[p.msg.opn_2b].max_value_bal == 
              && BalLeq(p.msg.bal_2b, s'.votes[p.msg.opn_2b].max_value_bal)
              && (s'.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s'.votes[p.msg.opn_2b].max_val == p.msg.val_2b);
}


}