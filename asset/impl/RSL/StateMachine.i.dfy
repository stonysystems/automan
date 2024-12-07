/**********************************************************************
AUTOMAN LOG

[Module] LiveRSL__StateMachine_i
**********************************************************************/

include ""


module Impl_LiveRSL__StateMachine_i 
{

	function method CHandleRequest(state: CAppState, request: CRequest) : (CAppState, CReply) 
		requires CAppStateIsValid(state)
		requires CRequestIsValid(request)
		ensures var (lr0, lr1) := HandleRequest(AbstractifyCAppStateToAppState(state), AbstractifyCRequestToRequest(request)); var (cr0, cr1) := CHandleRequest(state, request); CAppStateIsValid(cr0) && CReplyIsValid(cr1) && (AbstractifyCAppStateToAppState(cr0), AbstractifyCReplyToReply(cr1)) == (lr0, lr1)
	{
		var (new_state, reply) := 
			CAppHandleRequest(state, request.request); 		
		(new_state, CReply(request.client, request.seqno, reply))
	}

	function method CHandleRequestBatchHidden(state: CAppState, batch: CRequestBatch) : (seq<CAppState>, seq<CReply>) 
		requires CAppStateIsValid(state)
		requires CRequestBatchIsValid(batch)
		ensures var (states, replies) := CHandleRequestBatchHidden(state, batch); |states| == |batch| + 1 && |replies| == |batch| && (forall i :: 0 <= i && i < |batch| ==> replies[i].CReply?)
		decreases |batch|
		ensures var (lr0, lr1) := HandleRequestBatchHidden(AbstractifyCAppStateToAppState(state), AbstractifyCRequestBatchToRequestBatch(batch)); var (cr0, cr1) := CHandleRequestBatchHidden(state, batch); (forall i :: i in cr0 ==> CAppStateIsValid(i)) && (forall i :: i in cr1 ==> CReplyIsValid(i)) && (AbstractifySeq(cr0, AbstractifyCAppStateToAppState), AbstractifySeq(cr1, AbstractifyCReplyToReply)) == (lr0, lr1)
	{
		if |batch| == 0 then 
			([state], []) 
		else 
			var (restStates, restReplies) := 
				CHandleRequestBatchHidden(state, batch[ .. |batch| - 1]); 			
			var (new_state, reply) := 
				CAppHandleRequest(restStates[|restStates| - 1], batch[|batch| - 1].request); 			
			(restStates + [new_state], restReplies + [CReply(batch[|batch| - 1].client, batch[|batch| - 1].seqno, reply)])
	}

	function method CHandleRequestBatch(state: CAppState, batch: CRequestBatch) : (seq<CAppState>, seq<CReply>) 
		requires CAppStateIsValid(state)
		requires CRequestBatchIsValid(batch)
		ensures var (states, replies) := CHandleRequestBatch(state, batch); states[0] == state && |states| == |batch| + 1 && |replies| == |batch| && (forall i :: 0 <= i && i < |batch| ==> replies[i].CReply? && (states[i + 1], replies[i].reply) == CAppHandleRequest(states[i], batch[i].request) && replies[i].client == batch[i].client && replies[i].seqno == batch[i].seqno)
		ensures var (lr0, lr1) := HandleRequestBatch(AbstractifyCAppStateToAppState(state), AbstractifyCRequestBatchToRequestBatch(batch)); var (cr0, cr1) := CHandleRequestBatch(state, batch); (forall i :: i in cr0 ==> CAppStateIsValid(i)) && (forall i :: i in cr1 ==> CReplyIsValid(i)) && (AbstractifySeq(cr0, AbstractifyCAppStateToAppState), AbstractifySeq(cr1, AbstractifyCReplyToReply)) == (lr0, lr1)
	{
		var (states, replies) := 
			CHandleRequestBatchHidden(state, batch); 		
		(states, replies)
	}
}
