include ""


module Impl_LiveRSL__Types_i 
{
	type COperationNumber = int

	predicate COperationNumberIsAbstractable(s: COperationNumber) 
	{
		true
	}

	predicate COperationNumberIsValid(s: COperationNumber) 
	{
		COperationNumberIsAbstractable(s)
	}

	function AbstractifyCOperationNumberToOperationNumber(s: COperationNumber) : OperationNumber 
		requires COperationNumberIsAbstractable(s)
	{
		s
	}

	datatype CBallot = 
	CBallot(
		seqno: int, 
		proposer_id: int
	)

	predicate CBallotIsValid(s: CBallot) 
	{
		CBallotIsAbstractable(s)
	}

	predicate CBallotIsAbstractable(s: CBallot) 
	{
		true
	}

	function AbstractifyCBallotToBallot(s: CBallot) : Ballot 
		requires CBallotIsAbstractable(s)
	{
		Ballot(s.seqno, s.proposer_id)
	}

	datatype CRequest = 
	CRequest(
		client: EndPoint, 
		seqno: int, 
		request: CAppMessage
	)

	predicate CRequestIsValid(s: CRequest) 
	{
		CRequestIsAbstractable(s) 
		&& 
		EndPointIsValid(s.client) 
		&& 
		CAppMessageIsValid(s.request)
	}

	predicate CRequestIsAbstractable(s: CRequest) 
	{
		EndPointIsAbstractable(s.client) 
		&& 
		CAppMessageIsAbstractable(s.request)
	}

	function AbstractifyCRequestToRequest(s: CRequest) : Request 
		requires CRequestIsAbstractable(s)
	{
		Request(AbstractifyEndPointToNodeIdentity(s.client), s.seqno, AbstractifyCAppMessageToAppMessage(s.request))
	}

	datatype CReply = 
	CReply(
		client: EndPoint, 
		seqno: int, 
		reply: CAppMessage
	)

	predicate CReplyIsValid(s: CReply) 
	{
		CReplyIsAbstractable(s) 
		&& 
		EndPointIsValid(s.client) 
		&& 
		CAppMessageIsValid(s.reply)
	}

	predicate CReplyIsAbstractable(s: CReply) 
	{
		EndPointIsAbstractable(s.client) 
		&& 
		CAppMessageIsAbstractable(s.reply)
	}

	function AbstractifyCReplyToReply(s: CReply) : Reply 
		requires CReplyIsAbstractable(s)
	{
		Reply(AbstractifyEndPointToNodeIdentity(s.client), s.seqno, AbstractifyCAppMessageToAppMessage(s.reply))
	}
	type CRequestBatch = seq<CRequest>

	predicate CRequestBatchIsAbstractable(s: CRequestBatch) 
	{
		(forall i :: i in s ==> CRequestIsAbstractable(i))
	}

	predicate CRequestBatchIsValid(s: CRequestBatch) 
	{
		CRequestBatchIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> CRequestIsValid(i))
	}

	function AbstractifyCRequestBatchToRequestBatch(s: CRequestBatch) : RequestBatch 
		requires CRequestBatchIsAbstractable(s)
	{
		AbstractifySeq(s, AbstractifyCRequestToRequest)
	}
	type CReplyCache = map<EndPoint, CReply>

	predicate CReplyCacheIsAbstractable(s: CReplyCache) 
	{
		(forall i :: i in s ==> EndPointIsAbstractable(i) && CReplyIsAbstractable(s[i]))
	}

	predicate CReplyCacheIsValid(s: CReplyCache) 
	{
		CReplyCacheIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> EndPointIsValid(i) && CReplyIsValid(s[i]))
	}

	function AbstractifyCReplyCacheToReplyCache(s: CReplyCache) : ReplyCache 
		requires CReplyCacheIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyEndPointToNodeIdentity, AbstractifyReplyToCReply, AbstractifyNodeIdentityToEndPoint)
	}

	datatype CVote = 
	CVote(
		max_value_bal: CBallot, 
		max_val: CRequestBatch
	)

	predicate CVoteIsValid(s: CVote) 
	{
		CVoteIsAbstractable(s) 
		&& 
		CBallotIsValid(s.max_value_bal) 
		&& 
		CRequestBatchIsValid(s.max_val)
	}

	predicate CVoteIsAbstractable(s: CVote) 
	{
		CBallotIsAbstractable(s.max_value_bal) 
		&& 
		CRequestBatchIsAbstractable(s.max_val)
	}

	function AbstractifyCVoteToVote(s: CVote) : Vote 
		requires CVoteIsAbstractable(s)
	{
		Vote(AbstractifyCBallotToBallot(s.max_value_bal), AbstractifyCRequestBatchToRequestBatch(s.max_val))
	}
	type CVotes = map<COperationNumber, CVote>

	predicate CVotesIsAbstractable(s: CVotes) 
	{
		(forall i :: i in s ==> COperationNumberIsAbstractable(i) && CVoteIsAbstractable(s[i]))
	}

	predicate CVotesIsValid(s: CVotes) 
	{
		CVotesIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CVoteIsValid(s[i]))
	}

	function AbstractifyCVotesToVotes(s: CVotes) : Votes 
		requires CVotesIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyCOperationNumberToOperationNumber, AbstractifyVoteToCVote, AbstractifyOperationNumberToCOperationNumber)
	}

	datatype CearnerTuple = 
	CearnerTuple(
		received_2b_message_senders: set<EndPoint>, 
		candidate_learned_value: CRequestBatch
	)

	predicate CearnerTupleIsValid(s: CearnerTuple) 
	{
		CearnerTupleIsAbstractable(s) 
		&& 
		(forall i :: i in s.received_2b_message_senders ==> EndPointIsValid(i)) 
		&& 
		CRequestBatchIsValid(s.candidate_learned_value)
	}

	predicate CearnerTupleIsAbstractable(s: CearnerTuple) 
	{
		(forall i :: i in s.received_2b_message_senders ==> EndPointIsAbstractable(i)) 
		&& 
		CRequestBatchIsAbstractable(s.candidate_learned_value)
	}

	function AbstractifyCearnerTupleToLearnerTuple(s: CearnerTuple) : LearnerTuple 
		requires CearnerTupleIsAbstractable(s)
	{
		LearnerTuple(AbstractifySet(s.received_2b_message_senders, AbstractifyEndPointToNodeIdentity), AbstractifyCRequestBatchToRequestBatch(s.candidate_learned_value))
	}
	type CearnerState = map<COperationNumber, CearnerTuple>

	predicate CearnerStateIsAbstractable(s: CearnerState) 
	{
		(forall i :: i in s ==> COperationNumberIsAbstractable(i) && CearnerTupleIsAbstractable(s[i]))
	}

	predicate CearnerStateIsValid(s: CearnerState) 
	{
		CearnerStateIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CearnerTupleIsValid(s[i]))
	}

	function AbstractifyCearnerStateToLearnerState(s: CearnerState) : LearnerState 
		requires CearnerStateIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyCOperationNumberToOperationNumber, AbstractifyLearnerTupleToCearnerTuple, AbstractifyOperationNumberToCOperationNumber)
	}

	function method CBalLt(ba: CBallot, bb: CBallot) : bool 
		requires CBallotIsValid(ba)
		requires CBallotIsValid(bb)
		ensures var lr := BalLt(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb)); var cr := CBalLt(ba, bb); (cr) == (lr)
	{
		(ba.seqno < bb.seqno) || (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
	}

	function method CBalLeq(ba: CBallot, bb: CBallot) : bool 
		requires CBallotIsValid(ba)
		requires CBallotIsValid(bb)
		ensures var lr := BalLeq(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb)); var cr := CBalLeq(ba, bb); (cr) == (lr)
	{
		(ba.seqno < bb.seqno) || (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
	}
}
