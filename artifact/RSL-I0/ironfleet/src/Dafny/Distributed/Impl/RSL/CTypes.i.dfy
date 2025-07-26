include "../../Protocol/RSL/Types.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Common/Native/NativeTypes.i.dfy"
include "../Common/Util.i.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "AppInterface.i.dfy"

module LiveRSL__CTypes_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened Native__NativeTypes_i
  import opened LiveRSL__AppInterface_i
  import opened LiveRSL__Types_i
  import opened Common__NodeIdentity_i
  import opened Common__UdpClient_i
  import opened Common__Util_i
  import opened Collections__Maps_i
  import opened Collections__Sets_i
  import opened GenericRefinement_i
  import opened Concrete_NodeIdentity_i
  import opened Common__SeqIsUniqueDef_i

/************************** AutoMan Translation ************************/

  /** 1 + 0 */
  type COperationNumber = int

  /** 0 + 4 */
	predicate COperationNumberIsAbstractable(s: COperationNumber) 
	{
		true
	}

  /** 0 + 4 */
	predicate COperationNumberIsValid(s: COperationNumber) 
	{
		COperationNumberIsAbstractable(s)
	}

  /** 0 + 5 */
	function AbstractifyCOperationNumberToOperationNumber(s: COperationNumber) : OperationNumber 
    requires COperationNumberIsAbstractable(s)
	{
		s
	}

  /** 5 + 0 */
  datatype CBallot = 
	CBallot(
		seqno: int, 
		proposer_id: int
	)

  /** 0 + 4 */
	predicate CBallotIsValid(s: CBallot) 
	{
		CBallotIsAbstractable(s)
	}

  /** 0 + 4 */
	predicate CBallotIsAbstractable(s: CBallot) 
	{
		true
	}

  /** 0 + 5 */
	function AbstractifyCBallotToBallot(s: CBallot) : Ballot 
		requires CBallotIsAbstractable(s)
	{
		Ballot(s.seqno, s.proposer_id)
	}


  /** 6 + 0 */
	datatype CRequest = 
	CRequest(
		client: EndPoint, 
		seqno: int, 
		request: CAppMessage
	)

  /** 0 + 8 */
	predicate CRequestIsValid(s: CRequest) 
	{
		CRequestIsAbstractable(s) 
		&& 
		EndPointIsValid(s.client) 
		&& 
		CAppMessageIsValid(s.request)
	}

  /** 0 + 6 */
	predicate CRequestIsAbstractable(s: CRequest) 
	{
		EndPointIsAbstractable(s.client) 
		&& 
		CAppMessageIsAbstractable(s.request)
	}

  /** 0 + 5 */
	function AbstractifyCRequestToRequest(s: CRequest) : Request 
		requires CRequestIsAbstractable(s)
	{
		Request(AbstractifyEndPointToNodeIdentity(s.client), s.seqno, AbstractifyCAppMessageToAppMessage(s.request))
	}

  /** 1 + 0 */
  type CRequestBatch = seq<CRequest>

  /** 0 + 4 */
	predicate CRequestBatchIsAbstractable(s: CRequestBatch) 
	{
		(forall i :: i in s ==> i.CRequest? && CRequestIsAbstractable(i))
	}

  /** 0 + 4 + 1*/
	predicate CRequestBatchIsValid(s: CRequestBatch) 
	{
    |s| <= RequestBatchSizeLimit()
    && /* Manually added */
		CRequestBatchIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> i.CRequest? && CRequestIsValid(i))
	}

  /** 0 + 5 */
	function AbstractifyCRequestBatchToRequestBatch(s: CRequestBatch) : RequestBatch 
		requires CRequestBatchIsAbstractable(s)
	{
    AbstractifySeq(s, AbstractifyCRequestToRequest)
	}

  /** 6 + 0 */
  datatype CReply = 
	CReply(
		client: EndPoint, 
		seqno: int, 
		reply: CAppMessage
	)

  /** 0 + 8 */
	predicate CReplyIsValid(s: CReply) 
	{
		CReplyIsAbstractable(s) 
		&& 
		EndPointIsValid(s.client) 
		&& 
		CAppMessageIsValid(s.reply)
	}

  /** 0 + 6 */
	predicate CReplyIsAbstractable(s: CReply) 
	{
		EndPointIsAbstractable(s.client) 
		&& 
		CAppMessageIsAbstractable(s.reply)
	}

  /** 0 + 5 */
	function AbstractifyCReplyToReply(s: CReply) : Reply 
		requires CReplyIsAbstractable(s)
	{
		Reply(AbstractifyEndPointToNodeIdentity(s.client), s.seqno, AbstractifyCAppMessageToAppMessage(s.reply))
	}

  /** 1 + 0 */
  type CReplyCache = map<EndPoint, CReply>

  /** 0 + 4 */
	predicate CReplyCacheIsAbstractable(s: CReplyCache) 
	{
    (forall i :: i in s ==> EndPointIsAbstractable(i) && CReplyIsAbstractable(s[i]))
	}

  /** 0 + 5 + 1 */
	predicate CReplyCacheIsValid(s: CReplyCache) 
	{
    |s| < max_reply_cache_size()
    && /* Manually added */
		CReplyCacheIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> EndPointIsValid(i) && CReplyIsValid(s[i]))
	}

  /** 0 + 5 */
	function AbstractifyCReplyCacheToReplyCache(s: CReplyCache) : ReplyCache 
		requires CReplyCacheIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyEndPointToNodeIdentity, AbstractifyCReplyToReply, AbstractifyNodeIdentityToEndPoint)
	}

  /** 5 + 0 */
  datatype CVote = 
	CVote(
		max_value_bal: CBallot, 
		max_val: CRequestBatch
	)

  /** 0 + 8 */
	predicate CVoteIsValid(s: CVote) 
	{
		CVoteIsAbstractable(s) 
		&& 
		CBallotIsValid(s.max_value_bal) 
		&& 
		CRequestBatchIsValid(s.max_val)
	}

  /** 0 + 6 */
	predicate CVoteIsAbstractable(s: CVote) 
	{
		CBallotIsAbstractable(s.max_value_bal) 
		&& 
		CRequestBatchIsAbstractable(s.max_val)
	}

  /** 0 + 5 */
	function AbstractifyCVoteToVote(s: CVote) : Vote 
		requires CVoteIsAbstractable(s)
	{
		Vote(AbstractifyCBallotToBallot(s.max_value_bal), AbstractifyCRequestBatchToRequestBatch(s.max_val))
	}

  /** 1 + 0 */
  type CVotes = map<COperationNumber, CVote>

  /** 0 + 4 */
	predicate CVotesIsAbstractable(s: CVotes) 
	{
		(forall i :: i in s ==> COperationNumberIsAbstractable(i) && CVoteIsAbstractable(s[i]))
	}

  /** 0 + 6 + 1 */
	predicate CVotesIsValid(s: CVotes) 
	{
    /** Manually Added */
    |s| < max_votes_len()
    &&
		CVotesIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CVoteIsValid(s[i]))
	}

  /** 0 + 5 */
	function AbstractifyCVotesToVotes(s: CVotes) : Votes 
		requires CVotesIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyOperationNumberToCOperationNumber, AbstractifyCVoteToVote, AbstractifyCOperationNumberToOperationNumber)
	}


  
  /** 5 + 0 */
  datatype CLearnerTuple = 
	CLearnerTuple(
		received_2b_message_senders: set<EndPoint>, 
		candidate_learned_value: CRequestBatch
	)

  /** 0 + 8 */
	predicate CLearnerTupleIsValid(s: CLearnerTuple) 
	{
		CLearnerTupleIsAbstractable(s) 
		&& 
		(forall i :: i in s.received_2b_message_senders ==> EndPointIsValid(i)) 
		&& 
		CRequestBatchIsValid(s.candidate_learned_value)
	}

  /** 0 + 6 */
	predicate CLearnerTupleIsAbstractable(s: CLearnerTuple) 
	{
		(forall i :: i in s.received_2b_message_senders ==>  EndPointIsAbstractable(i)) 
		&& 
		CRequestBatchIsAbstractable(s.candidate_learned_value)
	}

  /** 0 + 5 */
	function AbstractifyCLearnerTupleToLearnerTuple(s: CLearnerTuple) : LearnerTuple 
		requires CLearnerTupleIsAbstractable(s)
	{
    LearnerTuple(AbstractifySet(s.received_2b_message_senders, AbstractifyEndPointToNodeIdentity), AbstractifyCRequestBatchToRequestBatch(s.candidate_learned_value))
	}

  /** 1 + 0 */
  type CLearnerState = map<COperationNumber, CLearnerTuple>

  /** 0 + 4 */
	predicate CLearnerStateIsAbstractable(s: CLearnerState) 
	{
		(forall i :: i in s ==> COperationNumberIsAbstractable(i) && CLearnerTupleIsAbstractable(s[i]))
	}

  /** 0 + 6 */
	predicate CLearnerStateIsValid(s: CLearnerState) 
	{
		CLearnerStateIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CLearnerTupleIsValid(s[i]))
	}

  /** 0 + 5 */
	function AbstractifyCLearnerStateToLearnerState(s: CLearnerState) : LearnerState 
		requires CLearnerStateIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyOperationNumberToCOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, AbstractifyCOperationNumberToOperationNumber)
	}


  /** 5 + 3 */
  function method {:opaque} CBalLt(ba: CBallot, bb: CBallot) : bool 
		requires CBallotIsValid(ba)
		requires CBallotIsValid(bb)
		ensures CBalLt(ba, bb) == BalLt(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb))
	{
		ba.seqno < bb.seqno || 
    (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
	}

  /** 5 + 3 */
	function method {:opaque} CBalLeq(ba: CBallot, bb: CBallot) : bool 
		requires CBallotIsValid(ba)
		requires CBallotIsValid(bb)
		ensures CBalLeq(ba, bb) == BalLeq(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb))
	{
		ba.seqno < bb.seqno || 
    (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
	}


/************************** AutoMan Translation End ************************/

  /** 0 + 0 + 5  */
  function AbstractifyOperationNumberToCOperationNumber(o:OperationNumber) : COperationNumber
    ensures AbstractifyOperationNumberToCOperationNumber(o) == o
  {
    o
  }


  function method RequestBatchSizeLimit() : int { 1000 }


  function max_reply_cache_size() : int { 256 }


  function method max_votes_len() : int { 1000 }

}
