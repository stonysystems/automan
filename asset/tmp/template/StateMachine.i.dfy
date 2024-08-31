include "ToBeFilled.i.dfy"
include "Types.i.dfy"

module Impl_LiveRSL__StateMachine_i {
 	import opened ToBeFilled
	import opened Impl_LiveRSL__Types_i

	function method CHandleRequest(
		state : CAppState ,
		request : CRequest) : (CAppState, CReply)
		requires CAppStateIsValid(state)
		requires CRequestIsValid(request)
		ensures var (r'0, r'1) := CHandleRequest(state, request); var (r0, r1) := HandleRequest(AbstractifyCAppStateToAppState(state), AbstractifyCRequestToRequest(request)); CAppStateIsValid(r'0) && CReplyIsValid(r'1) && (r0,r1) == (AbstractifyCAppStateToAppState(r'0),AbstractifyCReplyToReply(r'1))
	{
		var (new_state, reply) := HandleAppRequest(state, request.request); 
		(
			new_state,
			CReply(request.client, request.seqno, reply)
		)
	}

	function method CHandleRequestBatchHidden(
		state : CAppState ,
		batch : CRequestBatch) : (seq<CAppState>, seq<CReply>)
		requires CAppStateIsValid(state)
		requires CRequestBatchIsValid(batch)
		ensures var (r'0, r'1) := CHandleRequestBatchHidden(state, batch); var (r0, r1) := HandleRequestBatchHidden(AbstractifyCAppStateToAppState(state), AbstractifyCRequestBatchToRequestBatch(batch)); (forall i :: i in r'0 ==> CAppStateIsValid(i)) && (forall i :: i in r'1 ==> i.CReply? && CReplyIsValid(i)) && (r0,r1) == (AbstractifySeq(r'0, AbstractifyCAppStateToAppState),AbstractifySeq(r'1, AbstractifyCReplyToReply))
		ensures var (states, replies) := CHandleRequestBatchHidden(state, batch);  && |states| == |batch| + 1 && |replies| == |batch| && forall i :: 0 <= i < |batch| ==> replies[i].CReply?
		decreases |batch|
	{
		if |batch| == 0
		then 
			(
				[state],
				[]
			)
		else 
			var (restStates, restReplies) := CHandleRequestBatchHidden(state, batch[..|batch| - 1]); 
			var (new_state, reply) := HandleAppRequest(restStates[|restStates| - 1], batch[|batch| - 1].request); 
			(
				restStates + [new_state],
				restReplies + [CReply(batch[|batch| - 1].client, batch[|batch| - 1].seqno, reply)]
			)
	}

	function method CHandleRequestBatch(
		state : CAppState ,
		batch : CRequestBatch) : (seq<CAppState>, seq<CReply>)
		requires CAppStateIsValid(state)
		requires CRequestBatchIsValid(batch)
		ensures var (r'0, r'1) := CHandleRequestBatch(state, batch); var (r0, r1) := HandleRequestBatch(AbstractifyCAppStateToAppState(state), AbstractifyCRequestBatchToRequestBatch(batch)); (forall i :: i in r'0 ==> CAppStateIsValid(i)) && (forall i :: i in r'1 ==> i.CReply? && CReplyIsValid(i)) && (r0,r1) == (AbstractifySeq(r'0, AbstractifyCAppStateToAppState),AbstractifySeq(r'1, AbstractifyCReplyToReply))
		ensures var (states, replies) := CHandleRequestBatch(state, batch);  && states[0] == state && |states| == |batch| + 1 && |replies| == |batch| && (forall i :: 0 <= i < |batch| ==>  && replies[i].CReply? && ((states[i + 1],replies[i].reply) == HandleAppRequest(states[i], batch[i].request)) && replies[i].client == batch[i].client && replies[i].seqno == batch[i].seqno)
	{
		var (states, replies) := CHandleRequestBatchHidden(state, batch); 
		(
			states,
			replies
		)
	}
 
}
