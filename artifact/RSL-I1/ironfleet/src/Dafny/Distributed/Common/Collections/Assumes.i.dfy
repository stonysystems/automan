include "../../Impl/RSL/AppInterface.i.dfy"
include "../../Protocol/RSL/Executor.i.dfy"
include "../../Protocol/RSL/Message.i.dfy"
include "../../Impl/RSL/Broadcast.i.dfy"
include "../../Impl/RSL/CStateMachine.i.dfy"
include "../../Impl/Common/Util.i.dfy"
  // include "../../Common/Native/IoLemmas.i.dfy"
include "../../Protocol/RSL/StateMachine.i.dfy"
include "../../Protocol/RSL/Proposer.i.dfy"
include "../../Impl/RSL/ElectionImpl.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Protocol/RSL/Proposer.i.dfy"
include "../../Impl/RSL/ElectionImpl.i.dfy"
include "../../Impl/RSL/CConstants.i.dfy"

module Common_Assume_i{
  import opened Native__Io_s
    // import opened Native__IoLemmas_i
  import opened Native__NativeTypes_s
  import opened LiveRSL__AppInterface_i
  import opened LiveRSL__CMessage_i
  import opened LiveRSL__CMessageRefinements_i
  import opened LiveRSL__CTypes_i
  import opened LiveRSL__CPaxosConfiguration_i
  import opened LiveRSL__Environment_i
  import opened LiveRSL__Executor_i
    // import opened LiveRSL__CExecutor_i
  import opened LiveRSL__Message_i
  import opened LiveRSL__PacketParsing_i
  import opened LiveRSL__ConstantsState_i
  import opened LiveRSL__StateMachine_i
  import opened LiveRSL__Types_i
  import opened Impl__LiveRSL__Broadcast_i
  import opened Common__NodeIdentity_i
  import opened Common__UdpClient_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened Concrete_NodeIdentity_i
  import opened Collections__Maps_i
  import opened Logic__Option_i
  import opened Environment_s
  import opened AppStateMachine_i
  import opened Temporal__Temporal_s
  import opened LiveRSL__CStateMachine_i
  import opened GenericRefinement_i
  import opened LiveRSL__Broadcast_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__Election_i
  import opened LiveRSL__ElectionModel_i
  import opened LiveRSL__Proposer_i
  import opened Collections__Sets_i
  import opened Common__SeqIsUnique_i
  import opened Common__SeqIsUniqueDef_i

  predicate States_Equal(j:int, batch:CRequestBatch, states:seq<CAppState>, replies:seq<CReply>, g_states:seq<CAppState>)
		requires 0 <= j < |batch|
		requires 0 <= j < |states|-1
		requires 0 <= j < |g_states|-1
		requires 0 <= j < |replies|
	{
		&& states[j+1] == g_states[j+1]
		&& replies[j].CReply?
		&& ((states[j+1], replies[j].reply) == HandleAppRequest(states[j], batch[j].request))
		&& replies[j].client == batch[j].client
		&& replies[j].seqno == batch[j].seqno
	}

  predicate ReplyCacheUpdated(client:EndPoint, oldReplyCache:CReplyCache, newReplyCache:CReplyCache, batch:CRequestBatch, replies:seq<CReply>) 
		requires client in newReplyCache
		requires |batch| == |replies|
	{
		|| (client in oldReplyCache && newReplyCache[client] == oldReplyCache[client])
		|| (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch, replies))
	}

  predicate ClientIndexMatches(req_idx:int, client:EndPoint, newReplyCache:CReplyCache, batch:CRequestBatch, replies:seq<CReply>) 
		requires |batch| == |replies|
		requires client in newReplyCache
	{
		0 <= req_idx < |batch| && replies[req_idx].client == client && newReplyCache[client] == replies[req_idx] 
	}


  lemma {:axiom} lemma_CHandleRequestBatch_I1_loop(batch:CRequestBatch, replies:seq<CReply>, i:int, states:seq<CAppState>, state:CAppState, final_state:CAppState, repliesArr:array<CReply>,
												states_0:seq<CAppState>, replies_0:seq<CReply>, newReplyCache:CReplyCache, reply_cache:CReplyCache, reply_cache_mutable:MutableMap<EndPoint, CReply>)
		requires |states_0| == |batch| + 1
		requires |replies_0| == |batch|
		ensures 0 <= i as int <= |batch|
		ensures |replies| == i as int
		ensures |states| == (i as int) + 1
		ensures states[0] == state
		ensures final_state == states[i]
		ensures repliesArr.Length == |batch|
		ensures (forall i :: 0 <= i < |replies| ==> 
					&& replies[i].CReply?
					&& ((states[i+1], replies[i].reply) == HandleAppRequest(states[i], batch[i].request))
					&& replies[i].client == batch[i].client
					&& replies[i].seqno == batch[i].seqno
					&& replies[i] == repliesArr[i])
		ensures (forall j :: 0 <= j < i as int ==> States_Equal(j, batch, states, replies, states_0))
		ensures (forall j :: 0 <= j < i as int ==> states[j+1] == states_0[j+1])
		ensures replies == replies_0[..i]
		ensures CReplyCacheIsValid(newReplyCache)
		ensures forall client {:trigger ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)} :: 
						client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)
		ensures MutableMap.MapOf(reply_cache_mutable) == newReplyCache

	lemma {:axiom} lemma_CExecutorExecute_I1(newReplyCache:CReplyCache, new_cache:CReplyCache)
  		ensures newReplyCache == new_cache

  function method CSetOfMessage1b(
    S : set<CPacket>) : bool
    /*
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    ensures var bc := CSetOfMessage1b(S); var bl := LSetOfMessage1b(AbstractifySet(S, AbstractifyCPacketToRslPacket)); bl == bc
    */
  {
    forall p :: p in S ==> p.msg.CMessage_1b?
  }

  function {:opaque} CAllAcceptorsHadNoProposal(
    S : set<CPacket> ,
            opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CAllAcceptorsHadNoProposal(S, opn); var bl := LAllAcceptorsHadNoProposal(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    forall p :: p in S ==> !(opn in p.msg.votes)
  }

  function Cmax_balInS(
    c : CBallot ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CBallotIsValid(c)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := Cmax_balInS(c, S, opn); var bl := Lmax_balInS(AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    forall p :: p in S && opn in p.msg.votes ==> CBalLeq(p.msg.votes[opn].max_value_bal, c)
  }

  function CExistsBallotInS(
    v : CRequestBatch ,
    c : CBallot ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CRequestBatchIsValid(v)
    requires CBallotIsValid(c)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CExistsBallotInS(v, c, S, opn); var bl := LExistsBallotInS(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    exists p ::  && p in S && opn in p.msg.votes && p.msg.votes[opn].max_value_bal == c && p.msg.votes[opn].max_val == v
  }

  function CValIsHighestNumberedProposalAtBallot(
    v : CRequestBatch ,
    c : CBallot ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CRequestBatchIsValid(v)
    requires CBallotIsValid(c)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CValIsHighestNumberedProposalAtBallot(v, c, S, opn); var bl := LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {

    &&
      Cmax_balInS(c, S, opn)
    &&
      CExistsBallotInS(v, c, S, opn)
  }

  function CValIsHighestNumberedProposal(
    v : CRequestBatch ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CRequestBatchIsValid(v)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CValIsHighestNumberedProposal(v, S, opn); var bl := LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    // exists c :: CValIsHighestNumberedProposalAtBallot(v, c, S, opn)
    /* Manually added */
    exists p :: p in S && opn in p.msg.votes && CValIsHighestNumberedProposalAtBallot(v, p.msg.votes[opn].max_value_bal, S, opn)
  }

  lemma {:axiom} lemma_FindValWithHighestNumberedProposal(received_1b_packets:set<CPacket>, opn:COperationNumber, v:CRequestBatch)
  requires received_1b_packets != {}
  requires COperationNumberIsAbstractable(opn)
  requires CSetOfMessage1b(received_1b_packets)
  requires CPacketsIsAbstractable(received_1b_packets)
  requires (forall i :: i in received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
  requires SetIsInjective(received_1b_packets, AbstractifyCPacketToRslPacket)
  requires !CAllAcceptorsHadNoProposal(received_1b_packets, opn)
  requires forall p :: p in received_1b_packets ==> CVotesIsValid(p.msg.votes)
  ensures CRequestBatchIsAbstractable(v)
  ensures CRequestBatchIsValid(v)
  ensures LSetOfMessage1b(AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket))
  ensures LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn))
  ensures CValIsHighestNumberedProposal(v, received_1b_packets, opn)

}