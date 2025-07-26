include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"
include "Environment.i.dfy"
include "Quorum.i.dfy"
// include "Message1c.i.dfy"
include "Message2av.i.dfy"
include "QuorumOf2avs.i.dfy"
include "AcceptorState.i.dfy"
include "Received2av.i.dfy"
include "../../../Common/Collections/CountMatches.i.dfy"

module CommonProof__Message2b_i {
  import opened LiveByzRSL__Constants_i
  import opened LiveByzRSL__DistributedSystem_i
  import opened LiveByzRSL__Environment_i
  import opened LiveByzRSL__Types_i
  import opened LiveByzRSL__Configuration_i
  import opened LiveByzRSL__Acceptor_i
  import opened LiveByzRSL__Replica_i
  import opened LiveByzRSL__Message_i
  import opened CommonProof__AcceptorState_i
  import opened CommonProof__Assumptions_i
  import opened CommonProof__Constants_i
  import opened CommonProof__Actions_i
  import opened CommonProof__PacketSending_i
  import opened CommonProof__Environment_i
  import opened CommonProof__QuorumOf2avs_i
  import opened CommonProof__Quorum_i
  import opened CommonProof__Received2av_i
  // import opened CommonProof__Message1c_i
  import opened CommonProof__Message2av_i
  import opened Concrete_NodeIdentity_i
  import opened Temporal__Temporal_s
  import opened Environment_s
  import opened Collections__CountMatches_i
  import opened Collections__Sets_i

  // lemma lemma_2bMessageHasCorresponding2aMessage(
  //   b:Behavior<RslState>,
  //   c:LConstants,
  //   i:int,
  //   p_2b:RslPacket
  // ) returns (
  //     p_2avs:seq<RslPacket>
  //   )
  //   requires IsValidBehaviorPrefix(b, c, i)
  //   requires 0 <= i
  //   requires p_2b in b[i].environment.sentPackets
  //   requires p_2b.src in c.config.replica_ids
  //   requires p_2b.msg.RslMessage_2b?
  //   ensures  forall p_2av :: p_2av in p_2avs ==> 
  //             && p_2av in b[i].environment.sentPackets
  //             && p_2av.src in c.config.replica_ids
  //             && p_2av.msg.RslMessage_2av?
  //             && p_2av.msg.opn_2av == p_2b.msg.opn_2b
  //             && p_2av.msg.bal_2av == p_2b.msg.bal_2b
  //             && p_2av.msg.val_2av == p_2b.msg.val_2b
  //   decreases i
  // {
  //   if i == 0
  //   {
  //     return;
  //   }

  //   if p_2b in b[i-1].environment.sentPackets
  //   {
  //     p_2avs := lemma_2bMessageHasCorresponding2aMessage(b, c, i-1, p_2b);
  //     forall p_2av | p_2av in p_2avs
  //       ensures p_2av in b[i].environment.sentPackets
  //     {
  //       lemma_PacketStaysInSentPackets(b, c, i-1, i, p_2av);
  //     }
  //     return;
  //   }

  //   lemma_AssumptionsMakeValidTransition(b, c, i-1);
  //   lemma_ConstantsAllConsistent(b, c, i);
  //   lemma_ConstantsAllConsistent(b, c, i-1);

  //   var proposer_idx, ios := lemma_ActionThatSends2bIsProcess2a(b[i-1], b[i], p_2b);
  //   p_2a := ios[0].r;
  // }

  // lemma lemma_2bMessageHasCorresponding2aMessage(
  //   b:Behavior<RslState>,
  //   c:LConstants,
  //   i:int,
  //   p_2b:RslPacket
  // ) returns (
  //     p_2av:RslPacket
  //   )
  //   requires IsValidBehaviorPrefix(b, c, i)
  //   requires 0 <= i
  //   requires p_2b in b[i].environment.sentPackets
  //   requires p_2b.src in c.config.replica_ids
  //   requires p_2b.msg.RslMessage_2b?
  //   ensures  p_2av in b[i].environment.sentPackets
  //   ensures  p_2av.src in c.config.replica_ids
  //   ensures  p_2av.msg.RslMessage_2av?
  //   ensures  p_2av.msg.opn_2av == p_2b.msg.opn_2b
  //   ensures  p_2av.msg.bal_2av == p_2b.msg.bal_2b
  //   ensures  p_2av.msg.val_2av == p_2b.msg.val_2b
  //   decreases i
  // {
  //   if i == 0
  //   {
  //     return;
  //   }

  //   if p_2b in b[i-1].environment.sentPackets
  //   {
  //     p_2av := lemma_2bMessageHasCorresponding2aMessage(b, c, i-1, p_2b);
  //     lemma_PacketStaysInSentPackets(b, c, i-1, i, p_2av);
  //     return;
  //   }

  //   lemma_AssumptionsMakeValidTransition(b, c, i-1);
  //   lemma_ConstantsAllConsistent(b, c, i);
  //   lemma_ConstantsAllConsistent(b, c, i-1);

  //   var proposer_idx, ios := lemma_ActionThatSends2bIsProcess2av(b[i-1], b[i], p_2b);
  //   p_2a := ios[0].r;
  // }

  lemma lemma_IfValidQuorumOf2avsSequenceNowThenNext(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    qs:seq<QuorumOf2avs>
    )
    requires IsValidBehaviorPrefix(b, c, i+1)
    requires 0 <= i
    requires IsValidQuorumOf2avsSequence(b[i], qs)
    ensures  IsValidQuorumOf2avsSequence(b[i+1], qs)
  {
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i+1);

    forall opn | 0 <= opn < |qs|
      ensures qs[opn].opn == opn
      ensures IsValidQuorumOf2avs(b[i+1], qs[opn])
    {
      assert qs[opn].opn == opn && IsValidQuorumOf2avs(b[i], qs[opn]);
      forall idx | idx in qs[opn].indices
        ensures qs[opn].packets[idx] in b[i+1].environment.sentPackets
      {
        lemma_PacketStaysInSentPackets(b, c, i, i+1, qs[opn].packets[idx]);
      }
    }
  }

  lemma lemma_IfValidQuorumOf2avsNowThenNext(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    q:QuorumOf2avs
    )
    requires IsValidBehaviorPrefix(b, c, i+1)
    requires 0 <= i
    requires IsValidQuorumOf2avs(b[i], q)
    ensures  IsValidQuorumOf2avs(b[i+1], q)
  {
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i+1);

    assert IsValidQuorumOf2avs(b[i], q);
    forall idx | idx in q.indices
      ensures q.packets[idx] in b[i+1].environment.sentPackets
    {
      lemma_PacketStaysInSentPackets(b, c, i, i+1, q.packets[idx]);
    }
  }

  // lemma lemma_2bSentHasReceivedByzQuorum2avs(
  //   b:Behavior<RslState>,
  //   c:LConstants,
  //   i:int,
  //   idx:int
  // ) returns (
  //   q:QuorumOf2avs
  // )
  //   requires IsValidBehaviorPrefix(b, c, i)
  //   requires 0 <= i
  //   requires 0 <= idx < |b[i].replicas|
  //   requires var s := b[i].replicas[idx].replica.acceptor;
  //               && s.val_to_be_sent_2b.ValToBeSent2bKnown?
  //             // s.opn_to_be_send_2b in s.received_2avs
  //             // && exists v :: v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //             //                 && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v) >= LByzQuorumSize(s.constants.all.config)
  //   ensures IsValidQuorumOf2avs(b[i], q)
  //   // ensures var s := b[i].replicas[idx].replica.acceptor;
  //   //         // && q.opn == s.opn_to_be_send_2b
  //   //         && q.v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //   ensures var s := b[i].replicas[idx].replica.acceptor;
  //           && q.v == s.val_to_be_sent_2b.v
  //           // && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == q.v) >= LByzQuorumSize(s.constants.all.config)
  // {
  //   if i == 0
  //   {
  //     return;
  //   }

  //   lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  //   lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
  //   lemma_AssumptionsMakeValidTransition(b, c, i-1);

  //   var s := b[i-1].replicas[idx].replica.acceptor;
  //   var s' := b[i].replicas[idx].replica.acceptor;

  //   // if s'.opn_to_be_send_2b == s.opn_to_be_send_2b 
  //   // {
  //   //   q := lemma_2bSentHasReceivedByzQuorum2avs(b, c, i-1, idx);
  //   //   lemma_QuorumOf2avsStaysValid(b, c, i-1, i, q);
  //   //   return; 
  //   // }

  //   if s'.val_to_be_sent_2b == s.val_to_be_sent_2b 
  //   {
  //     q := lemma_2bSentHasReceivedByzQuorum2avs(b, c, i-1, idx);
  //     lemma_QuorumOf2avsStaysValid(b, c, i-1, i, q);
  //     return; 
  //   }

  //   var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  //   assert b[i-1].replicas[idx].nextActionIndex == 4;
  //   assert b[i-1].replicas[idx].nextActionIndex == 5;
  //   var opn := s.opn_to_be_send_2b;
  //   assert opn in s.received_2avs;
  //   assert |s.received_2avs[s.opn_to_be_send_2b].received_2av_message_senders| >= LByzQuorumSize(s.constants.all.config);
  //   assert IsByzQuorumSendSame2av(s.received_2avs[s.opn_to_be_send_2b].candidate_value, LByzQuorumSize(s.constants.all.config));
  //   assert Received2avsAreValid(s, s.opn_to_be_send_2b);

  //   var v :| v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //           && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v) >= LByzQuorumSize(s.constants.all.config);
  //   assert v in s'.received_2avs[s.opn_to_be_send_2b].candidate_value;
  //           // && CountMatchesInSeq(s'.received_2avs[s'.opn_to_be_send_2b].candidate_value, x => x == v) >= LByzQuorumSize(s'.constants.all.config);
    
  //   var senders := s.received_2avs[opn].received_2av_message_senders;

  //   var indices:set<int> := {};
  //   var packets:seq<RslPacket> := [];
  //   var sender_idx := 0;
  //   var dummy_packet := LPacket(c.config.replica_ids[0], c.config.replica_ids[0], RslMessage_1a(Ballot(0, 0)));
  //   while sender_idx < |c.config.replica_ids|
  //     invariant 0 <= sender_idx <= |c.config.replica_ids|
  //     invariant |packets| == sender_idx
  //     invariant forall sidx :: sidx in indices ==> && 0 <= sidx < sender_idx
  //                                         && var p := packets[sidx];
  //                                            && p.src == b[i].constants.config.replica_ids[sidx]
  //                                            && p.msg.RslMessage_2av?
  //                                            && p.msg.opn_2av == opn
  //                                            && v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //                                            && v in s'.received_2avs[s.opn_to_be_send_2b].candidate_value
  //                                           //  && p.msg.val_2b == v
  //                                           //  && p.msg.bal_2b == bal
  //                                            && p in b[i].environment.sentPackets
  //     invariant forall sidx {:trigger c.config.replica_ids[sidx] in senders} ::
  //                     0 <= sidx < sender_idx && c.config.replica_ids[sidx] in senders ==> sidx in indices
  //   {
  //     var sender := c.config.replica_ids[sender_idx];
  //     if sender in senders
  //     {
  //       assert opn in s.received_2avs;
  //       assert opn in b[i].replicas[idx].replica.acceptor.received_2avs;
  //       var sender_idx_unused, p := lemma_GetSent2avMessageFromAcceptorState(b, c, i, idx, opn, sender);
  //       assert ReplicasDistinct(c.config.replica_ids, sender_idx, GetReplicaIndex(p.src, c.config));
  //       packets := packets + [p];
  //       indices := indices + {sender_idx};
  //     }
  //     else 
  //     {
  //       packets := packets + [dummy_packet];
  //     }
  //     sender_idx := sender_idx + 1;
  //   }

  //   lemma_Received2avMessageSendersAlwaysValidReplicas(b, c, i-1, idx, opn);
  //   var alt_indices := lemma_GetIndicesFromNodes(senders, c.config);
  //   forall sidx | sidx in alt_indices
  //     ensures sidx in indices
  //   {
  //     assert 0 <= sidx < |c.config.replica_ids|;
  //     assert c.config.replica_ids[sidx] in senders;
  //   }
  //   SubsetCardinality(alt_indices, indices);

  //   // assert v in s'.received_2avs[s'.opn_to_be_send_2b].candidate_value;
  //   assert v in b[i].replicas[idx].replica.acceptor.received_2avs[s.opn_to_be_send_2b].candidate_value;

  //   q := QuorumOf2avs(c, indices, packets, opn, v);

  //   assert q.v in b[i].replicas[idx].replica.acceptor.received_2avs[s.opn_to_be_send_2b].candidate_value;
  //   assert s.opn_to_be_send_2b == s'.opn_to_be_send_2b;
  //   // assert q.v in b[i].replicas[idx].replica.acceptor.received_2avs[b[i].replicas[idx].replica.acceptor.opn_to_be_send_2b].candidate_value;
  // }

  // lemma lemma_2bSentHasReceivedByzQuorum2avs(
  //   b:Behavior<RslState>,
  //   c:LConstants,
  //   i:int,
  //   idx:int
  // ) returns (
  //   q:QuorumOf2avs
  // )
  //   requires IsValidBehaviorPrefix(b, c, i)
  //   requires 0 <= i
  //   requires 0 <= idx < |b[i].replicas|
  //   requires var s := b[i].replicas[idx].replica.acceptor;
  //               && s.val_to_be_sent_2b.ValToBeSent2bKnown?
  //             // s.opn_to_be_send_2b in s.received_2avs
  //             // && exists v :: v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //             //                 && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v) >= LByzQuorumSize(s.constants.all.config)
  //   ensures IsValidQuorumOf2avs(b[i], q)
  //   // ensures var s := b[i].replicas[idx].replica.acceptor;
  //   //         // && q.opn == s.opn_to_be_send_2b
  //   //         && q.v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //   ensures var s := b[i].replicas[idx].replica.acceptor;
  //           && q.v == s.val_to_be_sent_2b.v
  //           // && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == q.v) >= LByzQuorumSize(s.constants.all.config)
  // {
  //   if i == 0
  //   {
  //     return;
  //   }

  //   lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  //   lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
  //   lemma_AssumptionsMakeValidTransition(b, c, i-1);

  //   var s := b[i-1].replicas[idx].replica.acceptor;
  //   var s' := b[i].replicas[idx].replica.acceptor;

  //   // if s'.opn_to_be_send_2b == s.opn_to_be_send_2b 
  //   // {
  //   //   q := lemma_2bSentHasReceivedByzQuorum2avs(b, c, i-1, idx);
  //   //   lemma_QuorumOf2avsStaysValid(b, c, i-1, i, q);
  //   //   return; 
  //   // }

  //   if s'.val_to_be_sent_2b == s.val_to_be_sent_2b 
  //   {
  //     q := lemma_2bSentHasReceivedByzQuorum2avs(b, c, i-1, idx);
  //     lemma_QuorumOf2avsStaysValid(b, c, i-1, i, q);
  //     return; 
  //   }

  //   assert s'.val_to_be_sent_2b != s.val_to_be_sent_2b;
  //   assert s'.val_to_be_sent_2b.ValToBeSent2bKnown?;
  //   // assert s.val_to_be_sent_2b.ValToBeSent2bUnknown? || (s.val_to_be_sent_2b.ValToBeSent2bKnown? && s.val_to_be_sent_2b.v != s'.val_to_be_sent_2b.v);
  //   // assert s.val_to_be_sent_2b.ValToBeSent2bKnown?;
  //   assert s.val_to_be_sent_2b.ValToBeSent2bUnknown?; 

  //   var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  //   var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;

  //   // assert nextActionIndex == 4;
  //   // assert nextActionIndex == 5;
  //   assert nextActionIndex == 4;
  //   var opn := s.opn_to_be_send_2b;
  //   assert opn in s.received_2avs;
  //   assert |s.received_2avs[s.opn_to_be_send_2b].received_2av_message_senders| >= LByzQuorumSize(s.constants.all.config);
  //   assert IsByzQuorumSendSame2av(s.received_2avs[s.opn_to_be_send_2b].candidate_value, LByzQuorumSize(s.constants.all.config));
  //   assert Received2avsAreValid(s, s.opn_to_be_send_2b);

  //   var v :| v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //           && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v) >= LByzQuorumSize(s.constants.all.config);
  //   assert v in s'.received_2avs[s'.opn_to_be_send_2b].candidate_value
  //           && CountMatchesInSeq(s'.received_2avs[s'.opn_to_be_send_2b].candidate_value, x => x == v) >= LByzQuorumSize(s'.constants.all.config);
  //   var v2 := s'.val_to_be_sent_2b.v;
  //   assert v2 in s'.received_2avs[s'.opn_to_be_send_2b].candidate_value
  //           && CountMatchesInSeq(s'.received_2avs[s'.opn_to_be_send_2b].candidate_value, x => x == v) >= LByzQuorumSize(s'.constants.all.config);
  //   lemma_Chose2bValFromByzQuorumIsUnique(b, c, i, idx, v, v2);
  //   assert v == v2;
  //   assert v == s'.val_to_be_sent_2b.v;

  //   var senders := s.received_2avs[opn].received_2av_message_senders;

  //   var indices:set<int> := {};
  //   var packets:seq<RslPacket> := [];
  //   var sender_idx := 0;
  //   var dummy_packet := LPacket(c.config.replica_ids[0], c.config.replica_ids[0], RslMessage_1a(Ballot(0, 0)));
  //   while sender_idx < |c.config.replica_ids|
  //     invariant 0 <= sender_idx <= |c.config.replica_ids|
  //     invariant |packets| == sender_idx
  //     invariant forall sidx :: sidx in indices ==> && 0 <= sidx < sender_idx
  //                                         && var p := packets[sidx];
  //                                            && p.src == b[i].constants.config.replica_ids[sidx]
  //                                            && p.msg.RslMessage_2av?
  //                                            && p.msg.opn_2av == opn
  //                                            && v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //                                            && v in s'.received_2avs[s.opn_to_be_send_2b].candidate_value
  //                                           //  && p.msg.val_2av == v
  //                                           //  && p.msg.bal_2b == bal
  //                                            && p in b[i].environment.sentPackets
  //     invariant forall sidx {:trigger c.config.replica_ids[sidx] in senders} ::
  //                     0 <= sidx < sender_idx && c.config.replica_ids[sidx] in senders ==> sidx in indices
  //   {
  //     var sender := c.config.replica_ids[sender_idx];
  //     if sender in senders
  //     {
  //       assert opn in s.received_2avs;
  //       assert opn in b[i].replicas[idx].replica.acceptor.received_2avs;
  //       var sender_idx_unused, p := lemma_GetSent2avMessageFromAcceptorState(b, c, i, idx, opn, sender);
  //       assert ReplicasDistinct(c.config.replica_ids, sender_idx, GetReplicaIndex(p.src, c.config));
  //       var v3 := p.msg.val_2av;
  //       packets := packets + [p];
  //       indices := indices + {sender_idx};
  //     }
  //     else 
  //     {
  //       packets := packets + [dummy_packet];
  //     }
  //     sender_idx := sender_idx + 1;
  //   }

  //   lemma_Received2avMessageSendersAlwaysValidReplicas(b, c, i-1, idx, opn);
  //   var alt_indices := lemma_GetIndicesFromNodes(senders, c.config);
  //   forall sidx | sidx in alt_indices
  //     ensures sidx in indices
  //   {
  //     assert 0 <= sidx < |c.config.replica_ids|;
  //     assert c.config.replica_ids[sidx] in senders;
  //   }
  //   SubsetCardinality(alt_indices, indices);

  //   // assert v in s'.received_2avs[s'.opn_to_be_send_2b].candidate_value;
  //   assert v in b[i].replicas[idx].replica.acceptor.received_2avs[s.opn_to_be_send_2b].candidate_value;

  //   q := QuorumOf2avs(c, indices, packets, opn, v);

  //   assert q.v in b[i].replicas[idx].replica.acceptor.received_2avs[s.opn_to_be_send_2b].candidate_value;
  //   assert s.opn_to_be_send_2b == s'.opn_to_be_send_2b;
  //   // assert q.v in b[i].replicas[idx].replica.acceptor.received_2avs[b[i].replicas[idx].replica.acceptor.opn_to_be_send_2b].candidate_value;
  // }

  lemma lemma_CountMatchedValInReceived2avsOfDiffValNotExceedTheSeqSize(s:seq<RslPacket>, v1:RequestBatch, v2:RequestBatch)
    requires v1 != v2
    requires forall p :: p in s ==> p.msg.RslMessage_2av?
    ensures CountMatchedValInReceived2avs(s, v1) + CountMatchedValInReceived2avs(s, v2) <= |s|
  {
    var c1 := CountMatchedValInReceived2avs(s, v1);
    var c2 := CountMatchedValInReceived2avs(s, v2);

    if |s| == 0 {
      assert c1 == 0;
      assert c2 == 0;
      assert c1 + c2 <= |s|;
    } else {
      var tail := s[..|s|-1];
      lemma_CountMatchedValInReceived2avsOfDiffValNotExceedTheSeqSize(tail, v1, v2);
      assert CountMatchedValInReceived2avs(tail, v1) + CountMatchedValInReceived2avs(tail, v2) <= |tail|;
      assert |s| == |tail| + 1;
      // assert CountMatchedValInReceived2avs(tail, v1) <= CountMatchedValInReceived2avs(s, v1);
      assert CountMatchedValInReceived2avs(s, v1) + CountMatchedValInReceived2avs(s, v2) <= |s|;
    }
  }


  lemma lemma_Chose2bValFromByzQuorumIsUnique(
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
            s.acceptor.opn_to_be_send_2b in s.acceptor.received_2avs     
  requires var s := b[i].replicas[idx].replica;
           var opn := s.acceptor.opn_to_be_send_2b;
           && AcceptorStateCorrect(s.acceptor.received_2avs, s.acceptor.max_bal, s.acceptor.constants.all.config)
            && CountMatchedValInReceived2avs(s.acceptor.received_2avs[opn].received_2av_packets, v1) >= LByzQuorumSize(s.constants.all.config)
  requires var s := b[i].replicas[idx].replica;
           var opn := s.acceptor.opn_to_be_send_2b;
            && CountMatchedValInReceived2avs(s.acceptor.received_2avs[opn].received_2av_packets, v2) >= LByzQuorumSize(s.constants.all.config)
  ensures v1 == v2
{
  var s := b[i].replicas[idx].replica;
  var opn := s.acceptor.opn_to_be_send_2b;
  var quorum := LByzQuorumSize(s.constants.all.config);
  Lemma_TwoMinQuorumsIntersect(s.constants.all.config);
  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  assert quorum + quorum > |s.constants.all.config.replica_ids|;
  assert |s.acceptor.received_2avs[opn].received_2av_packets| <= |s.acceptor.constants.all.config.replica_ids|;
  if v1 != v2 
  {
    var c1 := CountMatchedValInReceived2avs(s.acceptor.received_2avs[opn].received_2av_packets, v1);
    var c2 := CountMatchedValInReceived2avs(s.acceptor.received_2avs[opn].received_2av_packets, v2);
    assert c1 >= quorum;
    assert c2 >= quorum;
    assert c1 + c2 > |s.constants.all.config.replica_ids|;
    lemma_CountMatchedValInReceived2avsOfDiffValNotExceedTheSeqSize(s.acceptor.received_2avs[opn].received_2av_packets, v1, v2);
    assert c1 + c2 <= |s.acceptor.received_2avs[opn].received_2av_packets|;
    assert false;
  }
}

  lemma lemma_2bSentHasReceivedByzQuorum2avs(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    idx:int
  ) returns (
    q:QuorumOf2avs
  )
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i
    requires 0 <= idx < |b[i].replicas|
    requires var s := b[i].replicas[idx].replica.acceptor;
                && s.val_to_be_sent_2b.ValToBeSent2bKnown?
              // s.opn_to_be_send_2b in s.received_2avs
              // && exists v :: v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
              //                 && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v) >= LByzQuorumSize(s.constants.all.config)
    ensures IsValidQuorumOf2avs(b[i], q)
    // ensures var s := b[i].replicas[idx].replica.acceptor;
    //         // && q.opn == s.opn_to_be_send_2b
    //         && q.v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
    ensures var s := b[i].replicas[idx].replica.acceptor;
            && q.v == s.val_to_be_sent_2b.v
            && q.opn == s.opn_to_be_send_2b
            && q.bal == s.val_to_be_sent_2b.bal
            // && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == q.v) >= LByzQuorumSize(s.constants.all.config)
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

    // // if s'.opn_to_be_send_2b == s.opn_to_be_send_2b 
    // // {
    // //   q := lemma_2bSentHasReceivedByzQuorum2avs(b, c, i-1, idx);
    // //   lemma_QuorumOf2avsStaysValid(b, c, i-1, i, q);
    // //   return; 
    // // }

    if s'.val_to_be_sent_2b == s.val_to_be_sent_2b 
    {
      q := lemma_2bSentHasReceivedByzQuorum2avs(b, c, i-1, idx);
      lemma_QuorumOf2avsStaysValid(b, c, i-1, i, q);
      return; 
    }

    // assert s'.val_to_be_sent_2b != s.val_to_be_sent_2b;
    // assert s'.val_to_be_sent_2b.ValToBeSent2bKnown?;
    // // assert s.val_to_be_sent_2b.ValToBeSent2bUnknown? || (s.val_to_be_sent_2b.ValToBeSent2bKnown? && s.val_to_be_sent_2b.v != s'.val_to_be_sent_2b.v);
    // // assert s.val_to_be_sent_2b.ValToBeSent2bKnown?;
    // assert s.val_to_be_sent_2b.ValToBeSent2bUnknown?; 

    var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
    var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;

    // // assert nextActionIndex == 4;
    // // assert nextActionIndex == 5;
    assert nextActionIndex == 4;
    var opn := s.opn_to_be_send_2b;
    var bal := s.max_bal;
    // assert opn in s.received_2avs;
    // assert |s.received_2avs[s.opn_to_be_send_2b].received_2av_message_senders| >= LByzQuorumSize(s.constants.all.config);
    // assert IsByzQuorumSendSame2av(s.received_2avs[s.opn_to_be_send_2b].candidate_value, LByzQuorumSize(s.constants.all.config));
    // assert Received2avsAreValid(s, s.opn_to_be_send_2b);

    var pkt :| pkt in s.received_2avs[opn].received_2av_packets
              && CountMatchedValInReceived2avs(s.received_2avs[opn].received_2av_packets, pkt.msg.val_2av) >= LByzQuorumSize(s.constants.all.config);
    var v := pkt.msg.val_2av;
    var v2 := s'.val_to_be_sent_2b.v;
    assert CountMatchedValInReceived2avs(s.received_2avs[opn].received_2av_packets, v) >= LByzQuorumSize(s.constants.all.config);
    assert CountMatchedValInReceived2avs(s.received_2avs[opn].received_2av_packets, v2) >= LByzQuorumSize(s.constants.all.config);
    lemma_Chose2bValFromByzQuorumIsUnique(b, c, i, idx, v, v2);
    assert v == s'.val_to_be_sent_2b.v;
    assert s'.val_to_be_sent_2b == ValToBeSent2bKnown(v, bal);

    var p2avs := s.received_2avs[opn].received_2av_packets;
    var indices:set<int> := {};
    var srcs:set<NodeIdentity> := {};

    var sender_idx := 0;
    var dummy_packet := LPacket(c.config.replica_ids[0], c.config.replica_ids[0], RslMessage_2av(Ballot(0, 0), 0, []));
    var packets:seq<RslPacket> := seq(|c.config.replica_ids|, idx => dummy_packet);
    assert |packets| == |c.config.replica_ids|;
    assert forall p :: p in packets ==> p.msg.RslMessage_2av?;

    assert AcceptorStateCorrect(s.received_2avs, s.max_bal, s.constants.all.config);
    assert (forall p :: p in p2avs ==> p.msg.RslMessage_2av?);
    assert (forall p :: p in p2avs ==> p.msg.opn_2av == opn);
    assert (forall i,j :: 0 <= i < |p2avs| && 0 <= j < |p2avs| && i != j 
                  ==> p2avs[i] != p2avs[j] && p2avs[i].src != p2avs[j].src);

    var count := 0;
    var temp_pkts:seq<RslPacket> := [];
    assert CountMatchedValInReceived2avs(s.received_2avs[opn].received_2av_packets, v) >= LByzQuorumSize(s.constants.all.config);

    var iter := 0;
    while iter < |p2avs|
      invariant 0 <= iter <= |p2avs|
      invariant |temp_pkts| == iter
      invariant temp_pkts == p2avs[..iter]
      invariant forall pkt :: pkt in temp_pkts ==> pkt.msg.RslMessage_2av?
      invariant forall iidx :: 0 <= iidx < iter && p2avs[iidx].msg.val_2av == v
                      ==> p2avs[iidx].src in srcs && GetReplicaIndex(p2avs[iidx].src, c.config) in indices
      invariant forall src :: src in srcs ==> src in c.config.replica_ids && GetReplicaIndex(src, c.config) in indices
      invariant forall j :: iter <= j < |p2avs| ==> (forall src :: src in srcs ==> p2avs[j].src != src)
      invariant forall j :: iter <= j < |p2avs| ==> (forall iidx :: iidx in indices ==> GetReplicaIndex(p2avs[j].src, c.config) != iidx)
      invariant count == CountMatchedValInReceived2avs(temp_pkts, v)
      invariant count == |srcs| == |indices|
      invariant |packets| == |c.config.replica_ids|
      invariant forall sidx :: sidx in indices ==> 
                  && 0 <= sidx < |c.config.replica_ids|
                  && var p := packets[sidx];
                  && p.src == b[i].constants.config.replica_ids[sidx]
                  && p.msg.RslMessage_2av?
                  && p.msg.val_2av == v
                  && p.msg.opn_2av == opn
                  && p.msg.bal_2av == bal
                  && p in b[i].environment.sentPackets
    {
      var p := p2avs[iter];
      assert count == CountMatchedValInReceived2avs(temp_pkts, v);
      lemma_CountMatchedValInReceived2avs_append_one(p2avs, v, iter);
    
      var index := GetReplicaIndex(p.src, c.config);
      if p.msg.val_2av == v {
        assert 0 <= index < |c.config.replica_ids|;
        assert |packets| == |c.config.replica_ids|;

        lemma_PacketInReceived2avWasSent(b, c, i, idx, opn, p);
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
        assert temp_pkts == p2avs[..iter+1];
        assert count == CountMatchedValInReceived2avs(p2avs[..iter], v) + 1;
        assert count == CountMatchedValInReceived2avs(p2avs[..iter+1], v);
        assert 0 <= index < |c.config.replica_ids|;
        assert p == packets[index];
        assert p.msg.RslMessage_2av?;
        assert p.msg.val_2av == v;
        assert p.msg.opn_2av == opn;
        assert p.msg.bal_2av == bal;
        assert p in b[i].environment.sentPackets;
      }
      else
      {
       assert 0 <= index < |c.config.replica_ids|;
        assert |packets| == |c.config.replica_ids|;
        packets := packets[index := p];
        temp_pkts := temp_pkts + [p];
        assert count == CountMatchedValInReceived2avs(p2avs[..iter], v);
        assert count == CountMatchedValInReceived2avs(p2avs[..iter+1], v); 
      }
      iter := iter + 1;
    }

    assert temp_pkts == p2avs;
    assert |srcs| >= LByzQuorumSize(s'.constants.all.config);
    assert |indices| >= LByzQuorumSize(s'.constants.all.config);
    q := QuorumOf2avs(c, indices, packets, bal, opn, v);
    assert (forall idx :: idx in q.indices ==> 
            // && 0 <= idx < |b[i].constants.config.replica_ids|
            && var p := q.packets[idx];
            // && p.src == b[i].constants.config.replica_ids[idx]
            && p.msg.RslMessage_2av?
            && p.msg.opn_2av == q.opn
            // && p.msg.val_2av == q.v
                               
            && p in b[i].environment.sentPackets);
  }

  lemma lemma_CountMatchedValInReceived2avs_append_one(s: seq<RslPacket>, v: RequestBatch, i: int)
    requires 0 <= i < |s|
    requires forall p :: p in s ==> p.msg.RslMessage_2av?
    ensures CountMatchedValInReceived2avs(s[..i+1], v) == CountMatchedValInReceived2avs(s[..i], v) + (if s[i].msg.val_2av == v then 1 else 0)
  {
    if i == 0 {
      assert s[..i+1] == [s[0]];
      assert CountMatchedValInReceived2avs(s[..i+1], v) == (if s[0].msg.val_2av == v then 1 else 0);
      assert CountMatchedValInReceived2avs(s[..i], v) == 0;
    } else {
      assert s[..i+1] == s[..i] + [s[i]]; 
      assert CountMatchedValInReceived2avs(s[..i+1], v) == CountMatchedValInReceived2avs(s[..i],v) + if v == s[i].msg.val_2av then 1 else 0;
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

  // lemma lemma_Chose2bValFromByzQuorumIsUnique(
  //   b:Behavior<RslState>,
  //   c:LConstants,
  //   i:int,
  //   idx:int,
  //   v1:RequestBatch,
  //   v2:RequestBatch
  // )
  //   requires IsValidBehaviorPrefix(b, c, i)
  //   requires 0 <= i
  //   requires 0 <= idx < |b[i].replicas|
  //   requires var s := b[i].replicas[idx].replica.acceptor;
  //             s.opn_to_be_send_2b in s.received_2avs
  //             && Received2avsAreValid(s, s.opn_to_be_send_2b)
  //   //           && exists v :: v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //   //                           && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v) >= LByzQuorumSize(s.constants.all.config)
  //   requires var s := b[i].replicas[idx].replica.acceptor;
  //             && v1 in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //             && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v1) >= LByzQuorumSize(s.constants.all.config)
  //   requires var s := b[i].replicas[idx].replica.acceptor;
  //             && v2 in s.received_2avs[s.opn_to_be_send_2b].candidate_value
  //             && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v2) >= LByzQuorumSize(s.constants.all.config)
  //   ensures v1 == v2
  // {
  //   var s := b[i].replicas[idx].replica.acceptor;
  //   var opn := s.opn_to_be_send_2b;
  //   var quorum := LByzQuorumSize(s.constants.all.config);
  //   Lemma_TwoByzantineQuorumsIntersect(s.constants.all.config);
  //   assert quorum + quorum > |s.constants.all.config.replica_ids|;
  //   assert |s.received_2avs[opn].candidate_value| <= |s.constants.all.config.replica_ids|;
  //   if v1 != v2 
  //   {
  //     var c1 := CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v1);
  //     var c2 := CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == v2);
  //     assert c1 >= quorum;
  //     assert c2 >= quorum;
  //     assert c1 + c2 > |s.constants.all.config.replica_ids|;
  //     lemma_CountMatchesInSeqOfDiffValNotExceedTheSeqSize(s.received_2avs[opn].candidate_value, v1, v2);
  //     assert c1 + c2 <= |s.received_2avs[opn].candidate_value|;
  //     assert false;
  //   }
  // }

  lemma lemma_2bSentIsMaybeSend2b(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    p:RslPacket,
    idx:int,
    ios:seq<RslIo>
  ) returns (
    q:QuorumOf2avs
  )
    requires IsValidBehaviorPrefix(b, c, i+1)
    requires 0 <= i
    requires 0 <= idx < |c.config.replica_ids|
    requires 0 <= idx < |b[i].replicas|
    requires LIoOpSend(p) in ios
    requires RslNext(b[i], b[i+1])
    requires b[i].environment.nextStep == LEnvStepHostIos(c.config.replica_ids[idx], ios)
    requires p.msg.RslMessage_2b?
    requires var s := b[i].replicas[idx].replica.acceptor;
                  && s.val_to_be_sent_2b.ValToBeSent2bKnown?
                  && s.val_to_be_sent_2b.bal == s.max_bal
              // && s.opn_to_be_send_2b in s.received_2avs
              // && |s.received_2avs[s.opn_to_be_send_2b].received_2av_message_senders| >= LByzQuorumSize(s.constants.all.config)
              // && IsByzQuorumSendSame2av(s.received_2avs[s.opn_to_be_send_2b].candidate_value, LByzQuorumSize(s.constants.all.config)) 
              // && Received2avsAreValid(s, s.opn_to_be_send_2b)
    requires LAcceptorSent2b(
              b[i].replicas[idx].replica.acceptor,
              b[i+1].replicas[idx].replica.acceptor,
              ExtractSentPacketsFromIos(ios)
            )
    ensures IsValidQuorumOf2avs(b[i], q)
    ensures q.opn == p.msg.opn_2b;
    ensures q.v == p.msg.val_2b
    ensures q.bal == p.msg.bal_2b
  {
    lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
    lemma_ReplicaConstantsAllConsistent(b, c, i+1, idx);

    q := lemma_2bSentHasReceivedByzQuorum2avs(b, c, i, idx);
    var s := b[i].replicas[idx].replica.acceptor;
    var opn := s.opn_to_be_send_2b;
  
    // assert q.v in s.received_2avs[s.opn_to_be_send_2b].candidate_value
    //         && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == q.v) >= LByzQuorumSize(s.constants.all.config);
    // assert p.msg.opn_2b == opn;
    // var val_2b := p.msg.val_2b;
    // assert val_2b in s.received_2avs[s.opn_to_be_send_2b].candidate_value
    //         && CountMatchesInSeq(s.received_2avs[s.opn_to_be_send_2b].candidate_value, x => x == val_2b) >= LByzQuorumSize(s.constants.all.config);
    // // assert p.msg.val_2b == v;
    // lemma_Chose2bValFromByzQuorumIsUnique(b, c, i, idx, q.v, val_2b);
    // assert q.v == val_2b;
  }

  lemma lemma_2bSentIsAllowed(
    b:Behavior<RslState>,
    c:LConstants,
    i:int,
    p:RslPacket
  ) returns (
    q:QuorumOf2avs
  )
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i
    requires p in b[i].environment.sentPackets
    requires p.src in c.config.replica_ids
    requires p.msg.RslMessage_2b?
    ensures IsValidQuorumOf2avs(b[i], q)
    ensures q.opn == p.msg.opn_2b
    ensures q.v == p.msg.val_2b
    ensures q.bal == p.msg.bal_2b
  {
    if i == 0 { return; }

    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
      q := lemma_2bSentIsAllowed(b, c, i-1, p);
      lemma_IfValidQuorumOf2avsNowThenNext(b, c, i-1, q);
      return;
    }

    assert b[i-1].environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in b[i-1].environment.nextStep.ios;
    var idx := GetReplicaIndex(b[i-1].environment.nextStep.actor, c.config);
    var ios := b[i-1].environment.nextStep.ios;
    var idx_alt :| RslNextOneReplica(b[i-1], b[i], idx_alt, ios);
    assert ReplicasDistinct(c.config.replica_ids, idx, idx_alt);

    var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;
    assert nextActionIndex == 5;
    q := lemma_2bSentIsMaybeSend2b(b, c, i-1, p, idx, ios);
    lemma_IfValidQuorumOf2avsNowThenNext(b, c, i-1, q);
  }

  
//   lemma lemma_test(s:seq<int>, v1:int, v2:int, N:int)
//     requires Quorum(N) <= |s| <= N
//     requires v1 in s && CountMatchesInSeq(s, x => x == v1) >= Quorum(N)
//     requires v2 in s && CountMatchesInSeq(s, x => x == v2) >= Quorum(N)
//     ensures v1 == v2
//   {
//     var q := Quorum(N);
//     assert q + q > N;
//     if v1 != v2 
//     {
//       var c1 := CountMatchesInSeq(s, x => x == v1);
//       var c2 := CountMatchesInSeq(s, x => x == v2);
//       assert c1 >= q;
//       assert c2 >= q;
//       assert c1 + c2 > N;
//       lemma_test2(s, v1, v2);
//       assert c1 + c2 <= |s|;
//       assert false;
//     }
//   }

// function Quorum(N:int) : int
//   {
//     N/2+1
//   }

//   lemma lemma_test2(s:seq<int>, v1:int, v2:int)
//     requires v1 != v2
//     ensures var c1 := CountMatchesInSeq(s, x => x == v1);
//             var c2 := CountMatchesInSeq(s, x => x == v2);
//             c1 + c2 <= |s|
//     {
//       var c1 := CountMatchesInSeq(s, x => x == v1);
//       var c2 := CountMatchesInSeq(s, x => x == v2);

//       if |s| == 0 {
//         assert c1 == 0;
//         assert c2 == 0;
//         assert c1 + c2 <= |s|;
//       } else {
//         var tail := s[1..];
//         lemma_test2(tail, v1, v2);
//       }
//     }

lemma lemma_CurrentVoteDoesNotExceedMaxBal(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  opn:OperationNumber,
  idx:int
)
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires opn in b[i].replicas[idx].replica.acceptor.votes
  ensures  BalLeq(b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal, b[i].replicas[idx].replica.acceptor.max_bal)
{
  if i == 0
  {
    return;
  }

  lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
  lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);

  var s := b[i-1].replicas[idx].replica.acceptor;
  var s' := b[i].replicas[idx].replica.acceptor;
  if s'.votes == s.votes && s'.max_bal == s.max_bal
  {
    lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, idx);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  if opn in s.votes
  {
    lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, idx);
  }
}

// /**
// opn 在 s 和 s' 的votes都存在
// 且bal相同，
// 证明：val也相同
//  */
// lemma lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(
//   b:Behavior<RslState>,
//   c:LConstants,
//   i:int,
//   opn:OperationNumber,
//   bal:Ballot,
//   idx:int
// )
//   requires IsValidBehaviorPrefix(b, c, i+1)
//   requires 0 <= i
//   requires 0 <= idx < |b[i].replicas|
//   requires 0 <= idx < |b[i+1].replicas|
//   requires opn in b[i].replicas[idx].replica.acceptor.votes
//   requires opn in b[i+1].replicas[idx].replica.acceptor.votes
//   requires b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_value_bal
//   ensures  b[i].replicas[idx].replica.acceptor.votes[opn].max_val == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_val
// {
//   lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
//   lemma_ReplicaConstantsAllConsistent(b, c, i+1, idx);
//   lemma_AssumptionsMakeValidTransition(b, c, i);

//   var s := b[i].replicas[idx].replica.acceptor;
//   var s' := b[i+1].replicas[idx].replica.acceptor;

//   if s'.votes[opn].max_val != s.votes[opn].max_val
//   {
//     var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i, idx);
//     var earlier_2a := lemma_Find1cThatCausedVote(b, c, i, idx, opn);
//     lemma_1cMessagesFromSameBallotAndOperationMatch(b, c, i+1, earlier_2a, ios[0].r);
//     assert false;
//   }
// }

// /**
// acceptor s发出了2b消息
// 证明目标：
// 2b.opn 在 s 的votes里
// 2b.bal <= s.votes[opn].max_val_bal
// 如果2b.bal == s.votes[opn].max_val_bal，那么2b.val == s.votes[opn].max_val
//  */
// lemma lemma_2bMessageImplicationsForCAcceptor(
//   b:Behavior<RslState>,
//   c:LConstants,
//   i:int,
//   p:RslPacket
// ) returns (
//     acceptor_idx:int
//   )
//   requires IsValidBehaviorPrefix(b, c, i)
//   requires 0 <= i
//   requires p in b[i].environment.sentPackets
//   requires p.src in c.config.replica_ids
//   requires p.msg.RslMessage_2b?
//   ensures  0 <= acceptor_idx < |c.config.replica_ids|
//   ensures  0 <= acceptor_idx < |b[i].replicas|
//   ensures  p.src == c.config.replica_ids[acceptor_idx]
//   ensures  BalLeq(p.msg.bal_2b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal)
//   ensures  var s := b[i].replicas[acceptor_idx].replica.acceptor;
//            p.msg.opn_2b >= s.log_truncation_point ==>
//               p.msg.opn_2b in s.votes
//               && BalLeq(p.msg.bal_2b, s.votes[p.msg.opn_2b].max_value_bal)
//               && (s.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s.votes[p.msg.opn_2b].max_val == p.msg.val_2b)
//   decreases i
// {
//   if i == 0
//   {
//     return;
//   }

//   lemma_AssumptionsMakeValidTransition(b, c, i-1);
//   lemma_ConstantsAllConsistent(b, c, i);
//   lemma_ConstantsAllConsistent(b, c, i-1);

//   var v := p.msg.val_2b;
//   var opn := p.msg.opn_2b;
//   var bal := p.msg.bal_2b;

//   if p in b[i-1].environment.sentPackets
//   {
//     acceptor_idx := lemma_2bMessageImplicationsForCAcceptor(b, c, i-1, p);
//     var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
//     var s' := b[i].replicas[acceptor_idx].replica.acceptor;

//     // var nextIndex := b[i-1].replicas[acceptor_idx].nextActionIndex;
//     // assert nextIndex == 
//     // assert p.msg.opn_2b in s.votes;
//     // assert BalLeq(p.msg.bal_2b, s.votes[p.msg.opn_2b].max_value_bal);
//     // assert (s.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s.votes[p.msg.opn_2b].max_val == p.msg.val_2b);

//     if s' != s
//     {
//       // var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, acceptor_idx);
//       if opn >= s'.log_truncation_point
//       {
//         assert p.msg.opn_2b in s'.votes;
//         lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, acceptor_idx);
//         if s'.votes[opn].max_value_bal == s.votes[opn].max_value_bal
//         {
//           lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, bal, acceptor_idx);
//         }
//         assert p.msg.opn_2b in s'.votes;
//         assert BalLeq(p.msg.bal_2b, s'.votes[p.msg.opn_2b].max_value_bal);
//         assert (s'.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s'.votes[p.msg.opn_2b].max_val == p.msg.val_2b);
//       }
//     }
//     return;
//   }

  
//   var ios:seq<RslIo>;
//   acceptor_idx, ios := lemma_ActionThatSends2bIsMaybeSend2b(b[i-1], b[i], p);

//   var q2avs := lemma_2bSentIsAllowed(b, c, i, p);
//   assert acceptor_idx in q2avs.indices;
//   var p2av := q2avs.packets[acceptor_idx];
//   var p1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i, p2av);

//   /**
//   1. 找到2b对应的q2av
//   2. 找到其中一个2av对应的1c
//   3. 证明处理1c时候，这几个是满足的
//    */
//   var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
//   var s' := b[i].replicas[acceptor_idx].replica.acceptor;
//   assert opn >= s.log_truncation_point ==> 
//           && opn in s.votes
//           && BalLeq(p.msg.bal_2b, s.votes[p.msg.opn_2b].max_value_bal)
//           && (s.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s.votes[p.msg.opn_2b].max_val == p.msg.val_2b);
//   if opn >= s'.log_truncation_point{
//     assert p.msg.opn_2b in s'.votes;
//     assert BalLeq(p.msg.bal_2b, s'.votes[p.msg.opn_2b].max_value_bal);
//     assert (s'.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s'.votes[p.msg.opn_2b].max_val == p.msg.val_2b);
//   }
// }

// /**
// acceptor s发出了2b消息
// 证明目标：
// 2b.opn 在 s 的votes里
// 2b.bal <= s.votes[opn].max_val_bal，为什么是<=呢？？？
// 如果2b.bal == s.votes[opn].max_val_bal，那么2b.val == s.votes[opn].max_val
//  */
// lemma lemma_2bMessageImplicationsForCAcceptor(
//   b:Behavior<RslState>,
//   c:LConstants,
//   i:int,
//   p:RslPacket
// ) returns (
//     acceptor_idx:int
//   )
//   requires IsValidBehaviorPrefix(b, c, i)
//   requires 0 <= i
//   requires p in b[i].environment.sentPackets
//   requires p.src in c.config.replica_ids
//   requires p.msg.RslMessage_2b?
//   ensures  0 <= acceptor_idx < |c.config.replica_ids|
//   ensures  0 <= acceptor_idx < |b[i].replicas|
//   ensures  p.src == c.config.replica_ids[acceptor_idx]
//   ensures  BalLeq(p.msg.bal_2b, b[i].replicas[acceptor_idx].replica.acceptor.max_bal)
//   ensures  var s := b[i].replicas[acceptor_idx].replica.acceptor;
//            p.msg.opn_2b >= s.log_truncation_point ==>
//               p.msg.opn_2b in s.votes
//               && BalLeq(p.msg.bal_2b, s.votes[p.msg.opn_2b].max_value_bal)
//               && (s.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s.votes[p.msg.opn_2b].max_val == p.msg.val_2b)
//   decreases i
// {
//   if i == 0
//   {
//     return;
//   }

//   lemma_AssumptionsMakeValidTransition(b, c, i-1);
//   lemma_ConstantsAllConsistent(b, c, i);
//   lemma_ConstantsAllConsistent(b, c, i-1);

//   var v := p.msg.val_2b;
//   var opn := p.msg.opn_2b;
//   var bal := p.msg.bal_2b;

//   if p in b[i-1].environment.sentPackets
//   {
//     acceptor_idx := lemma_2bMessageImplicationsForCAcceptor(b, c, i-1, p);
//     var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
//     var s' := b[i].replicas[acceptor_idx].replica.acceptor;

//     // var nextIndex := b[i-1].replicas[acceptor_idx].nextActionIndex;
//     // assert nextIndex == 
//     // assert p.msg.opn_2b in s.votes;
//     // assert BalLeq(p.msg.bal_2b, s.votes[p.msg.opn_2b].max_value_bal);
//     // assert (s.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s.votes[p.msg.opn_2b].max_val == p.msg.val_2b);

//     if s' != s
//     {
//       // var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, acceptor_idx);
//       if opn >= s'.log_truncation_point
//       {
//         assert p.msg.opn_2b in s'.votes;
//         lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, acceptor_idx);
//         if s'.votes[opn].max_value_bal == s.votes[opn].max_value_bal
//         {
//           lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i-1, opn, bal, acceptor_idx);
//         }
//         assert p.msg.opn_2b in s'.votes;
//         assert BalLeq(p.msg.bal_2b, s'.votes[p.msg.opn_2b].max_value_bal);
//         assert (s'.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s'.votes[p.msg.opn_2b].max_val == p.msg.val_2b);
//       }
//     }
//     assert p.msg.opn_2b >= s'.log_truncation_point ==>
//               p.msg.opn_2b in s'.votes
//               && BalLeq(p.msg.bal_2b, s'.votes[p.msg.opn_2b].max_value_bal)
//               && (s'.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s'.votes[p.msg.opn_2b].max_val == p.msg.val_2b);
//     return;
//   }

  
//   var ios:seq<RslIo>;
//   acceptor_idx, ios := lemma_ActionThatSends2bIsMaybeSend2b(b[i-1], b[i], p);

//   // var q2avs := lemma_2bSentIsAllowed(b, c, i, p);
//   // assert acceptor_idx in q2avs.indices;
//   // var p2av := q2avs.packets[acceptor_idx];
//   // var p1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i, p2av);
  
//   /**
//   1. 找到2b对应的q2av
//   2. 找到其中一个2av对应的1c
//   3. 证明处理1c时候，这几个是满足的
//    */
//   var s := b[i-1].replicas[acceptor_idx].replica.acceptor;
//   var s' := b[i].replicas[acceptor_idx].replica.acceptor;
//   var vbal := s.val_to_be_sent_2b.bal;
//   var vval := s.val_to_be_sent_2b.v;
//   assert p.msg.bal_2b == vbal == s.max_bal == s'.max_bal;
//   assert p.msg.val_2b == vval;
//   assert p.msg.bal_2b == s'.max_bal;
//   // if p.msg.opn_2b >= s'.log_truncation_point 
//   // {
//   //   if opn !in s.votes {
//   //     assert s'.votes[p.msg.opn_2b].max_value_bal == bal;
//   //     assert s'.votes[p.msg.opn_2b].max_val == vval;
//   //   }
//   //   else 
//   //   {
//   //     // if 
//   //   }
//   // }
//   assert p.msg.opn_2b >= s'.log_truncation_point ==>
//               p.msg.opn_2b in s'.votes
//               // && s'.votes[p.msg.opn_2b].max_value_bal == 
//               && BalLeq(p.msg.bal_2b, s'.votes[p.msg.opn_2b].max_value_bal)
//               && (s'.votes[p.msg.opn_2b].max_value_bal == p.msg.bal_2b ==> s'.votes[p.msg.opn_2b].max_val == p.msg.val_2b);
// }

  // lemma lemma_VoteWithOpnImplies1cSent(
  //   b:Behavior<RslState>,
  //   c:LConstants,
  //   i:int,
  //   idx:int,
  //   opn:OperationNumber
  // ) returns (
  //     p:RslPacket
  //   )
  //   requires IsValidBehaviorPrefix(b, c, i)
  //   requires 0 <= i
  //   requires 0 <= idx < |b[i].replicas|
  //   requires opn in b[i].replicas[idx].replica.acceptor.votes
  //   ensures  p in b[i].environment.sentPackets
  //   ensures  p.src in c.config.replica_ids
  //   ensures  p.msg.RslMessage_1c?
  //   ensures  p.msg.opn_1c == opn
  //   ensures  p.msg.bal_1c == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal
  //   ensures  p.msg.val_1c == b[i].replicas[idx].replica.acceptor.votes[opn].max_val
  //   decreases i
  // {
  //   if i == 0
  //   {
  //     return;
  //   }

  //   lemma_AssumptionsMakeValidTransition(b, c, i-1);
  //   lemma_ConstantsAllConsistent(b, c, i);
  //   lemma_ConstantsAllConsistent(b, c, i-1);

  //   var s := b[i-1].replicas[idx].replica.acceptor;
  //   var s' := b[i].replicas[idx].replica.acceptor;

  //   if opn in s.votes && s'.votes == s.votes 
  //   {
  //     p := lemma_VoteWithOpnImplies1cSent(b, c, i-1, idx, opn);
  //     return;
  //   }

  //   var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;
  //   assert nextActionIndex == 0 || nextActionIndex == 5;

  //   var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  //   if opn in s.votes && s'.votes[opn] == s.votes[opn]
  //   {
  //     p := lemma_VoteWithOpnImplies1cSent(b, c, i-1, idx, opn);
  //     return;
  //   }

  //   p := ios[0].r;
  // }

}
