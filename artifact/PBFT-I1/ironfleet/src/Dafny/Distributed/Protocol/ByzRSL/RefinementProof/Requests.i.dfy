include "../DistributedSystem.i.dfy"
include "../CommonProof/Requests.i.dfy"
include "../CommonProof/Message1b.i.dfy"
include "../CommonProof/Message2b.i.dfy"
include "../CommonProof/Message2av.i.dfy"
include "../CommonProof/Received1b.i.dfy"
include "Chosen.i.dfy"

module DirectRefinement__Requests_i {

import opened LiveByzRSL__Constants_i
import opened LiveByzRSL__DistributedSystem_i
import opened LiveByzRSL__Election_i
import opened LiveByzRSL__Environment_i
import opened LiveByzRSL__Proposer_i
import opened LiveByzRSL__Replica_i
import opened LiveByzRSL__Types_i
import opened LiveByzRSL__CheckValSafety_i
import opened CommonProof__Actions_i
import opened CommonProof__Assumptions_i
import opened CommonProof__Chosen_i
import opened CommonProof__Constants_i
import opened CommonProof__Environment_i
import opened CommonProof__QuorumOf2avs_i
import opened CommonProof__Message1b_i
import opened CommonProof__Message2av_i
import opened CommonProof__Message2b_i
import opened CommonProof__PacketSending_i
import opened CommonProof__Received1b_i
import opened CommonProof__Requests_i
import opened DirectRefinement__Chosen_i
import opened Temporal__Temporal_s
import opened Environment_s

lemma lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int,
  req:Request
  ) returns (
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires req in b[i].replicas[idx].replica.proposer.election_state.requests_received_this_epoch
  ensures  p in b[i].environment.sentPackets
  ensures  p.dst in c.config.replica_ids
  ensures  p.msg.RslMessage_Request?
  ensures  req == Request(p.src, p.msg.seqno_req, p.msg.val)
  decreases i
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var es := b[i-1].replicas[idx].replica.proposer.election_state;
  var es' := b[i].replicas[idx].replica.proposer.election_state;

  if req in es.requests_received_this_epoch
  {
    p := lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage(b, c, i-1, idx, req);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
    return;
  }

  assert req in es'.requests_received_this_epoch;
  assert req !in es.requests_received_this_epoch;

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;

  if nextActionIndex == 0
  {
    p := ios[0].r;
    assert IsValidLIoOp(ios[0], c.config.replica_ids[idx], b[i-1].environment);
    return;
  }
  // if nextActionIndex == 6
  // {
    var batch := b[i-1].replicas[idx].replica.executor.next_op_to_execute.v;
    assert ElectionStateReflectExecutedRequestBatch(es, es', batch);
    lemma_RemoveExecutedRequestBatchProducesSubsequence(es'.requests_received_this_epoch, es.requests_received_this_epoch, batch);
    assert false;
    return;
  // }

  // var acc := b[i-1].replicas[idx].replica.acceptor;
  // var acc' := b[i].replicas[idx].replica.acceptor;
  // // assert nextActionIndex == 10;
  // // assert LAcceptorMaybeSent2b(acc, acc', )
  // assert es == es';
  // assert false;
  // var batch := b[i-1].replicas[idx].replica.executor.next_op_to_execute.v;
  // assert ElectionStateReflectExecutedRequestBatch(es, es', batch);
  // lemma_RemoveExecutedRequestBatchProducesSubsequence(es'.requests_received_this_epoch, es.requests_received_this_epoch, batch);
  // assert false;
}

lemma lemma_RequestInRequestsReceivedPrevEpochsHasCorrespondingRequestMessage(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int,
  req:Request
  ) returns (
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires req in b[i].replicas[idx].replica.proposer.election_state.requests_received_prev_epochs
  ensures  p in b[i].environment.sentPackets
  ensures  p.dst in c.config.replica_ids
  ensures  p.msg.RslMessage_Request?
  ensures  req == Request(p.src, p.msg.seqno_req, p.msg.val)
  decreases i
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var es := b[i-1].replicas[idx].replica.proposer.election_state;
  var es' := b[i].replicas[idx].replica.proposer.election_state;

  if req in es.requests_received_prev_epochs
  {
    p := lemma_RequestInRequestsReceivedPrevEpochsHasCorrespondingRequestMessage(b, c, i-1, idx, req);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
    return;
  }
  if req in es.requests_received_this_epoch
  {
    p := lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage(b, c, i-1, idx, req);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;
  // assert nextActionIndex == 6 || nextActionIndex == 10;
  var batch := b[i-1].replicas[idx].replica.executor.next_op_to_execute.v;
  assert ElectionStateReflectExecutedRequestBatch(es, es', batch);
  lemma_RemoveExecutedRequestBatchProducesSubsequence(es'.requests_received_prev_epochs, es.requests_received_prev_epochs, batch);
  assert false;
}

lemma lemma_RequestInRequestQueueHasCorrespondingRequestMessage(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  idx:int,
  req:Request
  ) returns (
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires 0 <= idx < |b[i].replicas|
  requires req in b[i].replicas[idx].replica.proposer.request_queue
  ensures  p in b[i].environment.sentPackets
  ensures  p.dst in c.config.replica_ids
  ensures  p.msg.RslMessage_Request?
  ensures  req == Request(p.src, p.msg.seqno_req, p.msg.val)
  decreases i
{
  if i == 0 { return; }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);

  var s := b[i-1].replicas[idx].replica.proposer;
  var s' := b[i].replicas[idx].replica.proposer;

  if req in s.request_queue
  {
    p := lemma_RequestInRequestQueueHasCorrespondingRequestMessage(b, c, i-1, idx, req);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
    return;
  }
  if req in s.election_state.requests_received_prev_epochs
  {
    p := lemma_RequestInRequestsReceivedPrevEpochsHasCorrespondingRequestMessage(b, c, i-1, idx, req);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
    return;
  }
  if req in s.election_state.requests_received_this_epoch
  {
    p := lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage(b, c, i-1, idx, req);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
    return;
  }

  var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
  var nextActionIndex := b[i-1].replicas[idx].nextActionIndex;

  if nextActionIndex == 0 
  {
    p := ios[0].r;
    assert IsValidLIoOp(ios[0], c.config.replica_ids[idx], b[i-1].environment);
    return;
  }
  
  assert nextActionIndex == 10;
  // p := ios[0].r;
  // assert IsValidLIoOp(ios[0], c.config.replica_ids[idx], b[i-1].environment);
}

lemma lemma_RequestIn1bMessageHasCorrespondingRequestMessage(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p_1b:RslPacket,
  opn:OperationNumber,
  req_num:int
  ) returns (
  p_req:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_1b in b[i].environment.sentPackets
  requires p_1b.src in c.config.replica_ids
  requires p_1b.msg.RslMessage_1b?
  requires opn in p_1b.msg.votes
  requires 0 <= req_num < |p_1b.msg.votes[opn].max_val|
  ensures  p_req in b[i].environment.sentPackets
  ensures  p_req.dst in c.config.replica_ids
  ensures  p_req.msg.RslMessage_Request?
  ensures  p_1b.msg.votes[opn].max_val[req_num] == Request(p_req.src, p_req.msg.seqno_req, p_req.msg.val)
  decreases i, 1
{
  var p_2a := lemma_1bMessageWithOpnImplies1cSent(b, c, i, opn, p_1b);
  p_req := lemma_RequestIn1cMessageHasCorrespondingRequestMessage(b, c, i, p_2a, req_num);
}

lemma lemma_RequestIn1cMessageHasCorrespondingRequestMessage(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  p_1c:RslPacket,
  req_num:int
) returns (
  p_req:RslPacket
)
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires p_1c in b[i].environment.sentPackets
  requires p_1c.src in c.config.replica_ids
  requires p_1c.msg.RslMessage_1c?
  requires 0 <= req_num < |p_1c.msg.val_1c|
  ensures  p_req in b[i].environment.sentPackets
  ensures  p_req.dst in c.config.replica_ids
  ensures  p_req.msg.RslMessage_Request?
  ensures  p_1c.msg.val_1c[req_num] == Request(p_req.src, p_req.msg.seqno_req, p_req.msg.val)
  decreases i, 0
{
  if i == 0
  {
    return;
  }

  if p_1c in b[i-1].environment.sentPackets
  {
    p_req := lemma_RequestIn1cMessageHasCorrespondingRequestMessage(b, c, i-1, p_1c, req_num);
    lemma_PacketStaysInSentPackets(b, c, i-1, i, p_req);
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  lemma_AssumptionsMakeValidTransition(b, c, i-1);
  var idx, ios := lemma_ActionThatSends1cIsMaybeNominateValueAndSend1c(b[i-1], b[i], p_1c);

  var s := b[i-1].replicas[idx].replica.proposer;
  var s' := b[i].replicas[idx].replica.proposer;
  var log_truncation_point := b[i-1].replicas[idx].replica.acceptor.log_truncation_point;
  var sent_packets := ExtractSentPacketsFromIos(ios);

  if LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
  {
    assert LProposerNominateNewValueAndSend1c(s, s', ios[0].t, log_truncation_point, sent_packets);
    assert s.request_queue[req_num] == p_1c.msg.val_1c[req_num];
    p_req := lemma_RequestInRequestQueueHasCorrespondingRequestMessage(b, c, i-1, idx, s.request_queue[req_num]);
  }
  else 
  {
    assert LProposerNominateOldValueAndSend1c(s, s', log_truncation_point, sent_packets);
    var opn := s.next_operation_number_to_propose;
    var v := p_1c.msg.val_1c;
    var p_1b :| p_1b in s.received_1b_packets && opn in p_1b.msg.votes && p_1b.msg.votes[opn].max_val == v;
    lemma_PacketInReceived1bWasSent(b, c, i-1, idx, p_1b);
    p_req := lemma_RequestIn1bMessageHasCorrespondingRequestMessage(b, c, i-1, p_1b, opn, req_num);
  }
}

lemma lemma_DecidedRequestWasSentByClient(
  b:Behavior<RslState>,
  c:LConstants,
  i:int,
  qs:seq<QuorumOf2bs>,
  batches:seq<RequestBatch>,
  batch_num:int,
  req_num:int
  ) returns (
  p:RslPacket
  )
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires IsValidQuorumOf2bsSequence(b[i], qs)
  requires batches == GetSequenceOfRequestBatches(qs)
  requires 0 <= batch_num < |batches|
  requires 0 <= req_num < |batches[batch_num]|
  ensures  p in b[i].environment.sentPackets
  ensures  p.dst in c.config.replica_ids
  ensures  p.msg.RslMessage_Request?
  ensures  batches[batch_num][req_num] == Request(p.src, p.msg.seqno_req, p.msg.val)
  decreases i
{
  lemma_ConstantsAllConsistent(b, c, i);

  lemma_SequenceOfRequestBatchesNthElement(qs, batch_num);
  var batch := batches[batch_num];
  var request := batch[req_num];
  var q := qs[batch_num];
  var idx :| idx in q.indices;
  var packet_2b := q.packets[idx];
  assert packet_2b.msg.RslMessage_2b?;
  assert packet_2b.msg.val_2b == batch;

  // var packet_2a := lemma_2bMessageHasCorresponding2aMessage(b, c, i, packet_2b);

  var q2av := lemma_2bSentIsAllowed(b, c, i, packet_2b);
  assert IsValidQuorumOf2avs(b[i], q2av);
  var idx2 :| idx2 in q2av.indices;
  var packet_2av := q2av.packets[idx2];
  assert packet_2av.msg.RslMessage_2av?;
  assert packet_2av.msg.val_2av == packet_2b.msg.val_2b;
  assert packet_2av.msg.val_2av == batch;

  // p := lemma_RequestIn2aMessageHasCorrespondingRequestMessage(b, c, i, packet_2a, req_num);
  var packet_1c := lemma_2avMessageHasCorresponding1cMessage(b, c, i, packet_2av);

  p := lemma_RequestIn1cMessageHasCorrespondingRequestMessage(b, c, i, packet_1c, req_num);
}
    
}
