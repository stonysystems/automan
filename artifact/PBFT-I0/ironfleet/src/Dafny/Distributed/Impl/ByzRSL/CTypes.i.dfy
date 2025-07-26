include "../../Protocol/ByzRSL/Types.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Common/Native/NativeTypes.i.dfy"
include "../Common/Util.i.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "AppInterface.i.dfy"

module LiveByzRSL__CTypes_i {
  // import opened AppStateMachine_s
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened Native__NativeTypes_i
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__Types_i
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
    // |s| <= RequestBatchSizeLimit()
    && 
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
    // |s| < max_reply_cache_size()
    && 
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
    // |s| < max_votes_len()
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


  /** 5 + 3 */
  function method CBalLt(ba: CBallot, bb: CBallot) : bool 
		requires CBallotIsValid(ba)
		requires CBallotIsValid(bb)
		ensures var lr := BalLt(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb)); var cr := CBalLt(ba, bb); (cr) == (lr)
	{
		(ba.seqno < bb.seqno) || (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
	}

  /** 5 + 3 */
	function method CBalLeq(ba: CBallot, bb: CBallot) : bool 
		requires CBallotIsValid(ba)
		requires CBallotIsValid(bb)
		ensures var lr := BalLeq(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb)); var cr := CBalLeq(ba, bb); (cr) == (lr)
	{
		(ba.seqno < bb.seqno) || (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
	}


/************************** AutoMan Translation End ************************/

  /* ----------------------------------------- */

  /** 0 + 0 + 5  */
  function AbstractifyOperationNumberToCOperationNumber(o:OperationNumber) : COperationNumber
    ensures AbstractifyOperationNumberToCOperationNumber(o) == o
  {
    o
  }

  function method RequestBatchSizeLimit() : int { 1000 }

  function method max_reply_cache_size() : int { 256 }

  function method max_votes_len() : int { 1000 }

}
