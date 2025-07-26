include "../../Protocol/RSL/Types.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Common/Native/NativeTypes.i.dfy"
include "../Common/Util.i.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "AppInterface.i.dfy"

module LiveRSL__CTypes_i {
  // import opened AppStateMachine_s
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
		// requires COperationNumberIsAbstractable(s)(s)
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

  type CRequestBatch = seq<CRequest>

	predicate CRequestBatchIsAbstractable(s: CRequestBatch) 
	{
		(forall i :: i in s ==> i.CRequest? && CRequestIsAbstractable(i))
	}

	predicate CRequestBatchIsValid(s: CRequestBatch) 
	{
    |s| <= RequestBatchSizeLimit()
    && /* Manually added */
		CRequestBatchIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> i.CRequest? && CRequestIsValid(i))
	}

	function AbstractifyCRequestBatchToRequestBatch(s: CRequestBatch) : RequestBatch 
		requires CRequestBatchIsAbstractable(s)
	{
    AbstractifySeq(s, AbstractifyCRequestToRequest)
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

  type CReplyCache = map<EndPoint, CReply>

	predicate CReplyCacheIsAbstractable(s: CReplyCache) 
	{
    (forall i :: i in s ==> EndPointIsAbstractable(i) && CReplyIsAbstractable(s[i]))
	}

	predicate CReplyCacheIsValid(s: CReplyCache) 
	{
    |s| < max_reply_cache_size()
    && /* Manually added */
		CReplyCacheIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> EndPointIsValid(i) && CReplyIsValid(s[i]))
	}

	function AbstractifyCReplyCacheToReplyCache(s: CReplyCache) : ReplyCache 
		requires CReplyCacheIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyEndPointToNodeIdentity, AbstractifyCReplyToReply, AbstractifyNodeIdentityToEndPoint)
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
    /** Manually Added */
    |s| < max_votes_len()
    &&
		CVotesIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CVoteIsValid(s[i]))
	}

	function AbstractifyCVotesToVotes(s: CVotes) : Votes 
		requires CVotesIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyOperationNumberToCOperationNumber, AbstractifyCVoteToVote, AbstractifyCOperationNumberToOperationNumber)
	}


  

  datatype CLearnerTuple = 
	CLearnerTuple(
		received_2b_message_senders: set<EndPoint>, 
		candidate_learned_value: CRequestBatch
	)

	predicate CLearnerTupleIsValid(s: CLearnerTuple) 
	{
		CLearnerTupleIsAbstractable(s) 
		&& 
		(forall i :: i in s.received_2b_message_senders ==> EndPointIsValid(i)) 
		&& 
		CRequestBatchIsValid(s.candidate_learned_value)
	}

	predicate CLearnerTupleIsAbstractable(s: CLearnerTuple) 
	{
		(forall i :: i in s.received_2b_message_senders ==>  EndPointIsAbstractable(i)) 
		&& 
		CRequestBatchIsAbstractable(s.candidate_learned_value)
	}

	function AbstractifyCLearnerTupleToLearnerTuple(s: CLearnerTuple) : LearnerTuple 
		requires CLearnerTupleIsAbstractable(s)
	{
    LearnerTuple(AbstractifySet(s.received_2b_message_senders, AbstractifyEndPointToNodeIdentity), AbstractifyCRequestBatchToRequestBatch(s.candidate_learned_value))
	}

  type CLearnerState = map<COperationNumber, CLearnerTuple>

	predicate CLearnerStateIsAbstractable(s: CLearnerState) 
	{
		(forall i :: i in s ==> COperationNumberIsAbstractable(i) && CLearnerTupleIsAbstractable(s[i]))
	}

	predicate CLearnerStateIsValid(s: CLearnerState) 
	{
		CLearnerStateIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> COperationNumberIsValid(i) && CLearnerTupleIsValid(s[i]))
	}

	function AbstractifyCLearnerStateToLearnerState(s: CLearnerState) : LearnerState 
		requires CLearnerStateIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyOperationNumberToCOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, AbstractifyCOperationNumberToOperationNumber)
	}



  function method {:opaque} CBalLt(ba: CBallot, bb: CBallot) : bool 
		requires CBallotIsValid(ba)
		requires CBallotIsValid(bb)
		ensures CBalLt(ba, bb) == BalLt(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb))
	{
		ba.seqno < bb.seqno || 
    (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
	}

	function method {:opaque} CBalLeq(ba: CBallot, bb: CBallot) : bool 
		requires CBallotIsValid(ba)
		requires CBallotIsValid(bb)
		ensures CBalLeq(ba, bb) == BalLeq(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb))
	{
		ba.seqno < bb.seqno || 
    (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
	}


/************************** AutoMan Translation End ************************/

  /* ----------------------------------------- */

  function AbstractifyOperationNumberToCOperationNumber(o:OperationNumber) : COperationNumber
    ensures AbstractifyOperationNumberToCOperationNumber(o) == o
  {
    o
  }

  // type COperationNumber = int

  // predicate COperationNumberIsAbstractable(
  //   s : COperationNumber)

  // {
  //   true
  // }

  // predicate COperationNumberIsValid(
  //   s : COperationNumber)

  // {
  //   true
  // }

  // function AbstractifyCOperationNumberToOperationNumber(
  //   s : COperationNumber) : OperationNumber

  // {
  //   s
  // }


  /* ----------------------------------------- */

  // datatype CBallot =
  //   CBallot
  //   (
  //     seqno : int ,
  //     proposer_id : int
  //   )

  // predicate CBallotIsValid(
  //   s : CBallot)

  // {
  //   CBallotIsAbstractable(s)
  // }

  // predicate CBallotIsAbstractable(
  //   s : CBallot)

  // {
  //   true
  // }

  // function AbstractifyCBallotToBallot(
  //   s : CBallot) : Ballot
  //   requires CBallotIsAbstractable(s)
  // {
  //   Ballot(s.seqno, s.proposer_id)
  // }

  /* ----------------------------------------- */

  // datatype CRequest =
  //   CRequest
  //   (
  //     client : EndPoint ,
  //     seqno : int ,
  //     request : CAppMessage
  //   )

  // predicate CRequestIsValid(
  //   s : CRequest)

  // {
  //   CRequestIsAbstractable(s)
  //   &&
  //   EndPointIsValid(s.client)
  //   &&
  //   CAppMessageIsValid(s.request)
  // }

  // predicate CRequestIsAbstractable(
  //   s : CRequest)

  // {
  //   EndPointIsAbstractable(s.client)
  //   &&
  //   CAppMessageIsAbstractable(s.request)
  // }

  // function AbstractifyCRequestToRequest(
  //   s : CRequest) : Request
  //   requires CRequestIsAbstractable(s)
  // {
  //   Request(AbstractifyEndPointToNodeIdentity(s.client), s.seqno, AbstractifyCAppMessageToAppMessage(s.request))
  // }

  /* ----------------------------------------- */

  // datatype CReply =
  //   CReply
  //   (
  //     client : EndPoint ,
  //     seqno : int ,
  //     reply : CAppMessage
  //   )

  // predicate CReplyIsValid(
  //   s : CReply)

  // {
  //   CReplyIsAbstractable(s)
  //   &&
  //   EndPointIsValid(s.client)
  //   &&
  //   CAppMessageIsValid(s.reply)
  // }

  // predicate CReplyIsAbstractable(
  //   s : CReply)

  // {
  //   EndPointIsAbstractable(s.client)
  //   &&
  //   CAppMessageIsAbstractable(s.reply)
  // }

  // function AbstractifyCReplyToReply(
  //   s : CReply) : Reply
  //   requires CReplyIsAbstractable(s)
  // {
  //   Reply(AbstractifyEndPointToNodeIdentity(s.client), s.seqno, AbstractifyCAppMessageToAppMessage(s.reply))
  // }

  /* ----------------------------------------- */

  function method RequestBatchSizeLimit() : int { 1000 }

  // type CRequestBatch = seq<CRequest>

  // predicate CRequestBatchIsAbstractable(
  //   s : CRequestBatch)

  // {
  //   (forall i :: i in s ==> i.CRequest? && CRequestIsAbstractable(i))
  // }

  // predicate CRequestBatchIsValid(
  //   s : CRequestBatch)

  // {
  //   |s| <= RequestBatchSizeLimit()
  //   && /* Manually added */
  //   CRequestBatchIsAbstractable(s)
  //   &&
  //   (forall i :: i in s ==> i.CRequest? && CRequestIsValid(i))
  // }

  // function AbstractifyCRequestBatchToRequestBatch(
  //   s : CRequestBatch) : RequestBatch
  //   requires CRequestBatchIsAbstractable(s)
  // {
  //   AbstractifySeq(s, AbstractifyCRequestToRequest)
  // }

  /* ----------------------------------------- */

  function max_reply_cache_size() : int { 256 }

  // type CReplyCache = map<EndPoint, CReply>

  // predicate CReplyCacheIsAbstractable(
  //   s : CReplyCache)

  // {
  //   (forall i :: i in s ==> EndPointIsAbstractable(i) && s[i].CReply? && CReplyIsAbstractable(s[i]))
  // }

  // predicate CReplyCacheIsValid(
  //   s : CReplyCache)

  // {
  //   |s| < max_reply_cache_size()
  //   && /* Manually added */
  //   CReplyCacheIsAbstractable(s)
  //   &&
  //   (forall i :: i in s ==> EndPointIsValid(i) && s[i].CReply? && CReplyIsValid(s[i]))
  // }

  // function AbstractifyCReplyCacheToReplyCache(
  //   s : CReplyCache) : ReplyCache
  //   requires CReplyCacheIsAbstractable(s)
  // {
  //   AbstractifyMap(s, AbstractifyEndPointToNodeIdentity, AbstractifyCReplyToReply, AbstractifyNodeIdentityToEndPoint)
  // }

  /* ----------------------------------------- */

  function method max_votes_len() : int { 1000 }

  // datatype CVote =
  //   CVote
  //   (
  //     max_value_bal : CBallot ,
  //     max_val : CRequestBatch
  //   )

  // predicate CVoteIsValid(
  //   s : CVote)

  // {
  //   CVoteIsAbstractable(s)
  //   &&
  //   CBallotIsValid(s.max_value_bal)
  //   &&
  //   CRequestBatchIsValid(s.max_val)
  // }

  // predicate CVoteIsAbstractable(
  //   s : CVote)

  // {
  //   CBallotIsAbstractable(s.max_value_bal)
  //   &&
  //   CRequestBatchIsAbstractable(s.max_val)
  // }

  // function AbstractifyCVoteToVote(
  //   s : CVote) : Vote
  //   requires CVoteIsAbstractable(s)
  // {
  //   Vote(AbstractifyCBallotToBallot(s.max_value_bal), AbstractifyCRequestBatchToRequestBatch(s.max_val))
  // }

  /* ----------------------------------------- */

  // type CVotes = map<COperationNumber, CVote>

  // predicate CVotesIsAbstractable(
  //   s : CVotes)

  // {
  //   (forall i :: i in s ==> COperationNumberIsAbstractable(i) && s[i].CVote? && CVoteIsAbstractable(s[i]))
  // }

  // predicate CVotesIsValid(
  //   s : CVotes)

  // {
  //   |s| < max_votes_len()
  //   &&
  //   CVotesIsAbstractable(s)
  //   &&
  //   (forall i :: i in s ==> COperationNumberIsValid(i) && s[i].CVote? && CVoteIsValid(s[i]))
  // }

  // function AbstractifyCVotesToVotes(
  //   s : CVotes) : Votes
  //   requires CVotesIsAbstractable(s)
  // {
  //   AbstractifyMap(s, AbstractifyCOperationNumberToOperationNumber, AbstractifyCVoteToVote, AbstractifyOperationNumberToCOperationNumber)
  // }

  /* ----------------------------------------- */

  // datatype CLearnerTuple =
  //   CLearnerTuple
  //   (
  //     received_2b_message_senders : set<EndPoint> ,
  //     candidate_learned_value : CRequestBatch
  //   )

  // predicate CLearnerTupleIsValid(
  //   s : CLearnerTuple)

  // {
  //   CLearnerTupleIsAbstractable(s)
  //   &&
  //   (forall i :: i in s.received_2b_message_senders ==> i.EndPoint? && EndPointIsValid(i))
  //   &&
  //   CRequestBatchIsValid(s.candidate_learned_value)
  // }

  // predicate CLearnerTupleIsAbstractable(
  //   s : CLearnerTuple)

  // {
  //   (forall i :: i in s.received_2b_message_senders ==> i.EndPoint? && EndPointIsAbstractable(i))
  //   &&
  //   CRequestBatchIsAbstractable(s.candidate_learned_value)
  // }

  // function AbstractifyCLearnerTupleToLearnerTuple(
  //   s : CLearnerTuple) : LearnerTuple
  //   requires CLearnerTupleIsAbstractable(s)
  // {
  //   LearnerTuple(AbstractifySet(s.received_2b_message_senders, AbstractifyEndPointToNodeIdentity), AbstractifyCRequestBatchToRequestBatch(s.candidate_learned_value))
  // }

  /* ----------------------------------------- */

  // type CLearnerState = map<COperationNumber, CLearnerTuple>

  // predicate CLearnerStateIsAbstractable(
  //   s : CLearnerState)

  // {
  //   (forall i :: i in s ==> COperationNumberIsAbstractable(i) && s[i].CLearnerTuple? && CLearnerTupleIsAbstractable(s[i]))
  // }

  // predicate CLearnerStateIsValid(
  //   s : CLearnerState)

  // {
  //   CLearnerStateIsAbstractable(s)
  //   &&
  //   (forall i :: i in s ==> COperationNumberIsValid(i) && s[i].CLearnerTuple? && CLearnerTupleIsValid(s[i]))
  // }

  // function AbstractifyCLearnerStateToLearnerState(
  //   s : CLearnerState) : LearnerState
  //   requires CLearnerStateIsAbstractable(s)
  // {
  //   AbstractifyMap(s, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, AbstractifyOperationNumberToCOperationNumber)
  // }

  /* ----------------------------------------- */

  // function method {:opaque} CBalLt(
  //   ba : CBallot ,
  //   bb : CBallot) : bool
  //   requires CBallotIsValid(ba)
  //   requires CBallotIsValid(bb)
  //   ensures var bc := CBalLt(ba, bb); var bl := BalLt(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb)); bl == bc
  // {

  //   ||
  //     ba.seqno < bb.seqno
  //   ||
  //   (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
  // }

  // function method {:opaque} CBalLeq(
  //   ba : CBallot ,
  //   bb : CBallot) : bool
  //   requires CBallotIsValid(ba)
  //   requires CBallotIsValid(bb)
  //   ensures var bc := CBalLeq(ba, bb); var bl := BalLeq(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb)); bl == bc
  // {

  //   ||
  //     ba.seqno < bb.seqno
  //   ||
  //   (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
  // }

  /* ----------------------------------------- */

  lemma {:axiom} lemma_RequestValid(v:CRequest)
    ensures CRequestIsValid(v)

}
