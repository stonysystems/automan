include ""


module Impl_LiveRSL__Election_i 
{

	datatype CElectionState = 
	CElectionState(
		constants: CReplicaConstants, 
		current_view: CBallot, 
		current_view_suspectors: set<int>, 
		epoch_end_time: int, 
		epoch_length: int, 
		requests_received_this_epoch: seq<CRequest>, 
		requests_received_prev_epochs: seq<CRequest>
	)

	predicate CElectionStateIsValid(s: CElectionState) 
	{
		CElectionStateIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CBallotIsValid(s.current_view) 
		&& 
		(forall i :: i in s.requests_received_this_epoch ==> CRequestIsValid(i)) 
		&& 
		(forall i :: i in s.requests_received_prev_epochs ==> CRequestIsValid(i))
	}

	predicate CElectionStateIsAbstractable(s: CElectionState) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CBallotIsAbstractable(s.current_view) 
		&& 
		(forall i :: i in s.requests_received_this_epoch ==> CRequestIsAbstractable(i)) 
		&& 
		(forall i :: i in s.requests_received_prev_epochs ==> CRequestIsAbstractable(i))
	}

	function AbstractifyCElectionStateToElectionState(s: CElectionState) : ElectionState 
		requires CElectionStateIsAbstractable(s)
	{
		ElectionState(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.current_view), s.current_view_suspectors, s.epoch_end_time, s.epoch_length, AbstractifySeq(s.requests_received_this_epoch, AbstractifyCRequestToRequest), AbstractifySeq(s.requests_received_prev_epochs, AbstractifyCRequestToRequest))
	}
}
