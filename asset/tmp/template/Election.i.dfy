include "Constants.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "ToBeFilled.i.dfy"

module Impl_LiveRSL__Election_i {
 	import opened Impl_LiveRSL__Constants_i
	import opened Impl_LiveRSL__Environment_i
	import opened Impl_LiveRSL__Types_i
	import opened Impl_LiveRSL__Configuration_i
	import opened ToBeFilled
	import opened ToBeFilled

	datatype CElectionState = 
	CElectionState
	(
		constants : CReplicaConstants ,
		current_view : CBallot ,
		current_view_suspectors : set<int> ,
		epoch_end_time : int ,
		epoch_length : int ,
		requests_received_this_epoch : seq<CRequest> ,
		requests_received_prev_epochs : seq<CRequest>
	)

	predicate CElectionStateIsValid(
		s : CElectionState)
		
	{
		CElectionStateIsAbstractable(s)
		&&
		CReplicaConstantsIsValid(s.constants)
		&&
		CBallotIsValid(s.current_view)
		&&
		(forall i :: i in s.requests_received_this_epoch ==> i.CRequest? && CRequestIsValid(i))
		&&
		(forall i :: i in s.requests_received_prev_epochs ==> i.CRequest? && CRequestIsValid(i))
	}

	predicate CElectionStateIsAbstractable(
		s : CElectionState)
		
	{
		CReplicaConstantsIsAbstractable(s.constants)
		&&
		CBallotIsAbstractable(s.current_view)
		&&
		(forall i :: i in s.requests_received_this_epoch ==> i.CRequest? && CRequestIsAbstractable(i))
		&&
		(forall i :: i in s.requests_received_prev_epochs ==> i.CRequest? && CRequestIsAbstractable(i))
	}

	function AbstractifyCElectionStateToElectionState(
		s : CElectionState) : ElectionState
		requires CElectionStateIsAbstractable(s)
	{
		ElectionState(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.current_view), s.current_view_suspectors, s.epoch_end_time, s.epoch_length, AbstractifySeq(s.requests_received_this_epoch, AbstractifyCRequestToRequest), AbstractifySeq(s.requests_received_prev_epochs, AbstractifyCRequestToRequest))
	}

	function method CComputeSuccessorView(
		b : CBallot ,
		c : CConstants) : CBallot
		requires CBallotIsValid(b)
		requires CConstantsIsValid(c)
		ensures var r' := CComputeSuccessorView(b, c); var r := ComputeSuccessorView(AbstractifyCBallotToBallot(b), AbstractifyCConstantsToLConstants(c)); CBallotIsValid(r') && (r) == (AbstractifyCBallotToBallot(r'))
	{
		if b.proposer_id + 1 < |c.config.replica_ids|
		then 
			CBallot(b.seqno, b.proposer_id + 1)
		else 
			CBallot(b.seqno + 1, 0)
	}

	function method CBoundRequestSequence(
		s : seq<CRequest> ,
		lengthBound : CUpperBound) : seq<CRequest>
		requires (forall i :: i in s ==> i.CRequest? && CRequestIsValid(i))
		requires CUpperBoundIsValid(lengthBound)
		ensures var r' := CBoundRequestSequence(s, lengthBound); var r := BoundRequestSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCUpperBoundToUpperBound(lengthBound)); (forall i :: i in r' ==> i.CRequest? && CRequestIsValid(i)) && (r) == (AbstractifySeq(r', AbstractifyCRequestToRequest))
	{
		if lengthBound.CUpperBoundFinite? && 0 <= lengthBound.n < |s|
		then 
			s[..lengthBound.n]
		else 
			s
	}

	function method CRequestsMatch(
		r1 : CRequest ,
		r2 : CRequest) : bool
		requires CRequestIsValid(r1)
		requires CRequestIsValid(r2)
		ensures var bc := CRequestsMatch(r1, r2); var bl := RequestsMatch(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2)); (bl) == (bc)
	{
		r1.CRequest?
		&&
		r2.CRequest?
		&&
		r1.client == r2.client
		&&
		r1.seqno == r2.seqno
	}

	function method CRequestSatisfiedBy(
		r1 : CRequest ,
		r2 : CRequest) : bool
		requires CRequestIsValid(r1)
		requires CRequestIsValid(r2)
		ensures var bc := CRequestSatisfiedBy(r1, r2); var bl := RequestSatisfiedBy(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2)); (bl) == (bc)
	{
		r1.CRequest?
		&&
		r2.CRequest?
		&&
		r1.client == r2.client
		&&
		r1.seqno <= r2.seqno
	}

	function method CRemoveAllSatisfiedRequestsInSequence(
		s : seq<CRequest> ,
		r : CRequest) : seq<CRequest>
		requires (forall i :: i in s ==> i.CRequest? && CRequestIsValid(i))
		requires CRequestIsValid(r)
		ensures var r' := CRemoveAllSatisfiedRequestsInSequence(s, r); var r := RemoveAllSatisfiedRequestsInSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCRequestToRequest(r)); (forall i :: i in r' ==> i.CRequest? && CRequestIsValid(i)) && (r) == (AbstractifySeq(r', AbstractifyCRequestToRequest))
	{
		if |s| == 0
		then 
			[]
		else 
			if CRequestSatisfiedBy(s[0], r)
			then 
				CRemoveAllSatisfiedRequestsInSequence(s[1..], r)
			else 
				[s[0]] + CRemoveAllSatisfiedRequestsInSequence(s[1..], r)
	}

	function method CElectionStateInit(
		c : CReplicaConstants) : CElectionState
		requires |c.all.config.replica_ids| > 0
		requires CReplicaConstantsIsValid(c)
		ensures var es := CElectionStateInit(c); CElectionStateIsValid(es) && ElectionStateInit(AbstractifyCElectionStateToElectionState(es), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		CElectionState(constants := c, current_view := CBallot(1, 0), current_view_suspectors := {}, epoch_end_time := 0, epoch_length := c.all.params.baseline_view_timeout_period, requests_received_prev_epochs := [], requests_received_this_epoch := [])
	}

	function method CElectionStateProcessHeartbeat(
		es : CElectionState ,
		p : CPacket ,
		clock : int) : CElectionState
		requires CElectionStateIsValid(es)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_Heartbeat?
		ensures var es' := CElectionStateProcessHeartbeat(es, p, clock); CElectionStateIsValid(es') && ElectionStateProcessHeartbeat(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCPacketToRslPacket(p), clock)
	{
		if p.src !in es.constants.all.config.replica_ids
		then 
			es
		else 
			var sender_index := CGetReplicaIndex(p.src, es.constants.all.config); 
			if p.msg.bal_heartbeat == es.current_view && p.msg.suspicious
			then 
				es.(
					current_view_suspectors := es.current_view_suspectors + {sender_index}
				)
			else 
				if CBalLt(es.current_view, p.msg.bal_heartbeat)
				then 
					var new_epoch_length := UpperBoundedAdditionImpl(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); 
					es.(
						current_view := p.msg.bal_heartbeat,
						current_view_suspectors := (if p.msg.suspicious then {sender_index} else {}),
						epoch_length := new_epoch_length,
						epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val),
						requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
						requests_received_this_epoch := []
					)
				else 
					es
	}

	function method CElectionStateCheckForViewTimeout(
		es : CElectionState ,
		clock : int) : CElectionState
		requires CElectionStateIsValid(es)
		ensures var es' := CElectionStateCheckForViewTimeout(es, clock); CElectionStateIsValid(es') && ElectionStateCheckForViewTimeout(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), clock)
	{
		if clock < es.epoch_end_time
		then 
			es
		else 
			if |es.requests_received_prev_epochs| == 0
			then 
				var new_epoch_length := es.constants.all.params.baseline_view_timeout_period; 
				es.(
					epoch_length := new_epoch_length,
					epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val),
					requests_received_prev_epochs := es.requests_received_this_epoch,
					requests_received_this_epoch := []
				)
			else 
				es.(
					current_view_suspectors := es.current_view_suspectors + {es.constants.my_index},
					epoch_end_time := UpperBoundedAdditionImpl(clock, es.epoch_length, es.constants.all.params.max_integer_val),
					requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
					requests_received_this_epoch := []
				)
	}

	function method CElectionStateCheckForQuorumOfViewSuspicions(
		es : CElectionState ,
		clock : int) : CElectionState
		requires CElectionStateIsValid(es)
		ensures var es' := CElectionStateCheckForQuorumOfViewSuspicions(es, clock); CElectionStateIsValid(es') && ElectionStateCheckForQuorumOfViewSuspicions(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), clock)
	{
		if |es.current_view_suspectors| < CMinQuorumSize(es.constants.all.config) || !CLtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val)
		then 
			es
		else 
			var new_epoch_length := UpperBoundedAdditionImpl(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); 
			es.(
				current_view := CComputeSuccessorView(es.current_view, es.constants.all),
				current_view_suspectors := {},
				epoch_length := new_epoch_length,
				epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val),
				requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
				requests_received_this_epoch := []
			)
	}

	function method CElectionStateReflectReceivedRequest(
		es : CElectionState ,
		req : CRequest) : CElectionState
		requires CElectionStateIsValid(es)
		requires CRequestIsValid(req)
		ensures var es' := CElectionStateReflectReceivedRequest(es, req); CElectionStateIsValid(es') && ElectionStateReflectReceivedRequest(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestToRequest(req))
	{
		if (exists earlier_req :: earlier_req in es.requests_received_prev_epochs && CRequestsMatch(earlier_req, req))
		then 
			es
		else 
			if (exists earlier_req :: earlier_req in es.requests_received_this_epoch && CRequestsMatch(earlier_req, req))
			then 
				es
			else 
				es.(
					requests_received_this_epoch := CBoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val)
				)
	}

	function method CRemoveExecutedRequestBatch(
		reqs : seq<CRequest> ,
		batch : CRequestBatch) : seq<CRequest>
		requires (forall i :: i in reqs ==> i.CRequest? && CRequestIsValid(i))
		requires CRequestBatchIsValid(batch)
		ensures var r' := CRemoveExecutedRequestBatch(reqs, batch); var r := RemoveExecutedRequestBatch(AbstractifySeq(reqs, AbstractifyCRequestToRequest), AbstractifyCRequestBatchToRequestBatch(batch)); (forall i :: i in r' ==> i.CRequest? && CRequestIsValid(i)) && (r) == (AbstractifySeq(r', AbstractifyCRequestToRequest))
		decreases |batch|
	{
		if |batch| == 0
		then 
			reqs
		else 
			CRemoveExecutedRequestBatch(CRemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), batch[1..])
	}

	function method CElectionStateReflectExecutedRequestBatch(
		es : CElectionState ,
		batch : CRequestBatch) : CElectionState
		requires CElectionStateIsValid(es)
		requires CRequestBatchIsValid(batch)
		ensures var es' := CElectionStateReflectExecutedRequestBatch(es, batch); CElectionStateIsValid(es') && ElectionStateReflectExecutedRequestBatch(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestBatchToRequestBatch(batch))
	{
		es.(
			requests_received_prev_epochs := CRemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch),
			requests_received_this_epoch := CRemoveExecutedRequestBatch(es.requests_received_this_epoch, batch)
		)
	}
 
}
