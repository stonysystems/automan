include "../../Protocol/RSL/Types.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Common/Native/NativeTypes.i.dfy"
include "../Common/Util.i.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "AppInterface.i.dfy"

module LiveRSL__CTypes_i {
import opened AppStateMachine_s
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Native__NativeTypes_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__Types_i
import opened Common__NodeIdentity_i
import opened Common__NetClient_i
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
		request: CAppRequest
	)

	predicate CRequestIsValid(s: CRequest) 
	{
		CRequestIsAbstractable(s) 
		&& 
		EndPointIsValid(s.client) 
		&& 
		CAppRequestMarshallable(s.request)
	}

	predicate CRequestIsAbstractable(s: CRequest) 
	{
		EndPointIsAbstractable(s.client) 
		&& 
		CAppRequestIsAbstractable(s.request)
	}

	function AbstractifyCRequestToRequest(s: CRequest) : Request 
		requires CRequestIsAbstractable(s)
	{
		Request(AbstractifyEndPointToNodeIdentity(s.client), s.seqno, AbstractifyCAppRequestToAppRequest(s.request))
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
		reply: CAppReply
	)

	predicate CReplyIsValid(s: CReply) 
	{
		CReplyIsAbstractable(s) 
		&& 
		EndPointIsValid(s.client) 
		&& 
		CAppReplyMarshallable(s.reply)
	}

	predicate CReplyIsAbstractable(s: CReply) 
	{
		EndPointIsAbstractable(s.client) 
		&& 
		CAppReplyIsAbstractable(s.reply)
	}

	function AbstractifyCReplyToReply(s: CReply) : Reply 
		requires CReplyIsAbstractable(s)
	{
		Reply(AbstractifyEndPointToNodeIdentity(s.client), s.seqno, AbstractifyCAppReplyToAppReply(s.reply))
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

 function AbstractifyOperationNumberToCOperationNumber(o:OperationNumber) : COperationNumber
    ensures AbstractifyOperationNumberToCOperationNumber(o) == o
  {
    o
  }

  function method RequestBatchSizeLimit() : int { 1000 }

  function method max_votes_len() : int { 1000 }

  function max_reply_cache_size() : int { 256 }


// type COperationNumber = uint64
// // datatype COperationNumber = COperationNumber(n:uint64)

// function COperationNumberValid(c:COperationNumber) : bool
// {
//   &&  0 <= c < 0xffff_ffff_ffff_ffff
// }

// function AbstractifyCOperationNumberToOperationNumber(opn:COperationNumber) : OperationNumber
//   ensures (0 <= AbstractifyCOperationNumberToOperationNumber(opn) <= 0xffff_ffff_ffff_ffff)
// {
//   opn as int
// }

// function RefineOperationNumberToCOperationNumber(o:OperationNumber) : COperationNumber 
//   // requires 0 <= o < 0x1_0000_0000_0000_0000
//   ensures (0 <= o < 0x1_0000_0000_0000_0000) ==> RefineOperationNumberToCOperationNumber(o) == o as uint64
// {
//   if (0 <= o  && o < 0x1_0000_0000_0000_0000) then
//     o as uint64
//   else
//     var co:COperationNumber :| (true); co
// }

// datatype CBallot = CBallot(seqno:uint64, proposer_id:uint64)

// function CBallotValid(b:CBallot) : bool
// {
//   && b.seqno < 0xffff_ffff_ffff_ffff
//   && b.proposer_id < 0xffff_ffff_ffff_ffff
// }

// predicate CBallotIsAbstractable(ballot:CBallot)
// {
//   && ballot.CBallot?     // OBSERVE: Always true, but seems necessary to avoid errors below
//   && ballot.proposer_id <= 0xFFFF_FFFF_FFFF_FFFF // We don't support more than 2^64-1 replicas.  Such is life.
//   //&& EndPointUint64Representation(ballot.proposer_id)
// }

// function AbstractifyCBallotToBallot(ballot:CBallot) : Ballot
//   // the specification of the ballot does not account for a null state.
//   requires CBallotIsAbstractable(ballot)
// {
//   //Ballot(int(ballot.seqno), AbstractifyUint64ToNodeIdentity(ballot.proposer_id))
//   Ballot(ballot.seqno as int, ballot.proposer_id as int)
// }

// datatype CRequest = CRequest(client:EndPoint, seqno:uint64, request:CAppRequest)

// // 这里涉及到common的EndPoint和CAppRequest，怎么验证这些是valid的？？？
// // function CRequestValid(r:CRequest) : bool
// // {
// //   CAppRequestMarshallable(r.request)
// // }

// predicate CRequestIsAbstractable(c:CRequest)
// {
//   EndPointIsAbstractable(c.client) && CAppRequestIsAbstractable(c.request)
// }

// predicate CRequestValid(c:CRequest)
// {
//   && c.CRequest? ==> EndPointIsValidPublicKey(c.client) 
//   && CAppRequestMarshallable(c.request)
// }

// function AbstractifyCRequestToRequest(c:CRequest) : Request
//   requires CRequestIsAbstractable(c)
// {
//   Request(AbstractifyEndPointToNodeIdentity(c.client), c.seqno as int, AbstractifyCAppRequestToAppRequest(c.request))  
// }

// datatype CReply   = CReply  (client:EndPoint, seqno:uint64, reply:CAppReply)

// function CReplyValid(c:CReply) : bool
// {
//   // r.seqno < 0xffff_ffff_ffff_ffff
//    c.CReply? ==> EndPointIsValidPublicKey(c.client) && CAppReplyMarshallable(c.reply)
// }

// predicate CReplyIsAbstractable(c:CReply)
// {
//   EndPointIsAbstractable(c.client) && CAppReplyIsAbstractable(c.reply)
// }

// function AbstractifyCReplyToReply(c:CReply) : Reply
//   requires CReplyIsAbstractable(c)
// {
//   Reply(AbstractifyEndPointToNodeIdentity(c.client), c.seqno as int, AbstractifyCAppReplyToAppReply(c.reply))
// }

// type CRequestBatch = seq<CRequest>

// // && (forall cr :: cr in r ==> CAppRequestMarshallable(cr.request))
// // function CRequestBatchValid(r:CRequestBatch) : bool
// // {
// //   0 < |r| < 0xffff_ffff_ffff_ffff && (forall req :: req in r ==> CAppRequestMarshallable(req.request))
// // }
// function RequestBatchSizeLimit() : int { 100 }

// predicate CRequestBatchValid(c:CRequestBatch)
// {
//   && |c| <= RequestBatchSizeLimit()
//   && (forall req :: req in c ==> CAppRequestMarshallable(req.request))
//   && (forall cr :: cr in c ==> CRequestValid(cr)) // && |c| <= RequestBatchSizeLimit()
// }

// predicate CRequestsSeqIsAbstractable(cvals:seq<CRequest>)
// {
//   forall cval :: cval in cvals ==> CRequestIsAbstractable(cval)
// }

// lemma lemma_AbstractifyCRequestToRequest_isInjective()
//   ensures forall v1, v2 :: CRequestIsAbstractable(v1) && CRequestIsAbstractable(v2) && AbstractifyCRequestToRequest(v1) == AbstractifyCRequestToRequest(v2) ==> v1 == v2
// {
// //  assert forall u1:uint64, u2:uint64 :: u1 as int == u2 as int ==> u1 == u2;
//   lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
// }

// function {:opaque} AbstractifyCRequestsSeqToRequestsSeq(cvals:seq<CRequest>) : seq<Request>
//   requires CRequestsSeqIsAbstractable(cvals)
//   ensures |cvals| == |AbstractifyCRequestsSeqToRequestsSeq(cvals)|
//   ensures forall i {:trigger AbstractifyCRequestsSeqToRequestsSeq(cvals)[i]} :: 0 <= i < |cvals| ==> AbstractifyCRequestToRequest(cvals[i]) == AbstractifyCRequestsSeqToRequestsSeq(cvals)[i]
//   ensures  forall c :: CRequestIsAbstractable(c) ==> (c in cvals <==> AbstractifyCRequestToRequest(c) in AbstractifyCRequestsSeqToRequestsSeq(cvals))
// {   
//   lemma_AbstractifyCRequestToRequest_isInjective();
//   if |cvals| == 0 then []
//   else [AbstractifyCRequestToRequest(cvals[0])] + AbstractifyCRequestsSeqToRequestsSeq(cvals[1..])
// }

// predicate CRequestBatchIsAbstractable(c:CRequestBatch)
// {
//   CRequestsSeqIsAbstractable(c)
// }

// function {:opaque} AbstractifyCRequestBatchToRequestBatch(cvals:CRequestBatch) : RequestBatch
//   requires CRequestsSeqIsAbstractable(cvals)
//   ensures |cvals| == |AbstractifyCRequestBatchToRequestBatch(cvals)|
//   ensures forall i :: 0 <= i < |cvals| ==> AbstractifyCRequestToRequest(cvals[i]) == AbstractifyCRequestBatchToRequestBatch(cvals)[i]
//   ensures forall c :: CRequestIsAbstractable(c) ==> (c in cvals <==> AbstractifyCRequestToRequest(c) in AbstractifyCRequestBatchToRequestBatch(cvals))
// {
//   AbstractifyCRequestsSeqToRequestsSeq(cvals)
// }

// type CReplyCache = map<EndPoint, CReply>

// function CReplyCacheValid(r:CReplyCache) : bool
// {
//   |r| < 0xffff_ffff_ffff_ffff && (forall rep :: rep in r ==> CReplyValid(r[rep]))
// }

// predicate CReplyCacheIsAbstractable(m:CReplyCache)
// {
//   forall e {:trigger EndPointIsValidPublicKey(e)} :: e in m ==> EndPointIsValidPublicKey(e) && CReplyIsAbstractable(m[e])
// }

// function {:opaque} AbstractifyCReplyCacheToReplyCache(m:CReplyCache) : ReplyCache
//   requires CReplyCacheIsAbstractable(m)
// {
//   assert forall e :: e in m ==> EndPointIsValidPublicKey(e);
//   lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
//   // var test:CReply->Reply := (AbstractifyCReplyToReply as CReply->Reply);
//   AbstractifyMap(m, AbstractifyEndPointToNodeIdentity, AbstractifyCReplyToReply, RefineNodeIdentityToEndPoint)
// }


// lemma lemma_AbstractifyCReplyCacheToReplyCache_properties(m:CReplyCache)
//   requires CReplyCacheIsAbstractable(m)
//   ensures  m == map [] ==> AbstractifyCReplyCacheToReplyCache(m) == map []
//   ensures  forall e {:trigger e in m}{:trigger e in AbstractifyCReplyCacheToReplyCache(m)} :: (e in m <==> EndPointIsValidPublicKey(e) && e in AbstractifyCReplyCacheToReplyCache(m))
//   ensures  forall e {:trigger e in m, EndPointIsValidPublicKey(e)}{:trigger e in AbstractifyCReplyCacheToReplyCache(m)} :: (e !in m && EndPointIsValidPublicKey(e) ==> e !in AbstractifyCReplyCacheToReplyCache(m))
//   ensures  forall e {:trigger AbstractifyCReplyToReply(m[e])}{:trigger AbstractifyCReplyCacheToReplyCache(m)[e]} :: e in m ==> AbstractifyCReplyCacheToReplyCache(m)[e] == AbstractifyCReplyToReply(m[e])
//   ensures  forall re :: re in AbstractifyCReplyCacheToReplyCache(m) ==> re in m
//   ensures  forall e, r {:trigger EndPointIsValidPublicKey(e), CReplyValid(r)} :: EndPointIsValidPublicKey(e) && CReplyValid(r) ==> 
//               var rm  := AbstractifyCReplyCacheToReplyCache(m);
//               var rm' := AbstractifyCReplyCacheToReplyCache(m[e := r]);
//               rm' == AbstractifyCReplyCacheToReplyCache(m)[AbstractifyEndPointToNodeIdentity(e) := AbstractifyCReplyToReply(r)]
//   ensures forall e {:trigger RemoveElt(m,e)} :: 
//               (EndPointIsValidPublicKey(e) && NodeIdentityIsRefinable(AbstractifyEndPointToNodeIdentity(e))
//                && RefineNodeIdentityToEndPoint(AbstractifyEndPointToNodeIdentity(e)) == e && e in m) ==>
//           var rm  := AbstractifyCReplyCacheToReplyCache(m); 
//           var rm' := AbstractifyCReplyCacheToReplyCache(RemoveElt(m, e));
//           rm' == RemoveElt(rm, e)
// {
//   assert forall e :: e in m ==> EndPointIsValidPublicKey(e);
//   reveal AbstractifyCReplyCacheToReplyCache();
//   lemma_AbstractifyMap_properties(m, AbstractifyEndPointToNodeIdentity, AbstractifyCReplyToReply, RefineNodeIdentityToEndPoint);
// }


// datatype CVote = CVote(max_value_bal:CBallot, max_val:CRequestBatch)

// function max_votes_len() : int { 8 }

// function CVoteValid(v:CVote) : bool
// {
//   // && CBallotValid(v.max_value_bal)
//   && CRequestBatchValid(v.max_val)
// }

// datatype CVotes = CVotes(v:map<COperationNumber,CVote>)

// function CVotesValid(votes:CVotes) : bool
// {
//   && |votes.v| < max_votes_len()
//   && (forall o :: o in votes.v ==> CVoteValid(votes.v[o]))
// }

// predicate CVoteIsAbstractable(vote:CVote)
// {
//   && vote.CVote?     // OBSERVE: Always true, but seems necessary to avoid errors below
//   && CBallotIsAbstractable(vote.max_value_bal)
//   && CRequestBatchIsAbstractable(vote.max_val)
// }

// function AbstractifyCVoteToVote(vote:CVote) : Vote
//   requires CVoteIsAbstractable(vote)
// {
//   Vote(AbstractifyCBallotToBallot(vote.max_value_bal), AbstractifyCRequestBatchToRequestBatch(vote.max_val))
// }


// predicate CVotesIsAbstractable(votes:CVotes)
// {
//   forall i :: i in votes.v ==> CVoteIsAbstractable(votes.v[i])
// }

// lemma lemma_AbstractifyMapOfThings<T>(m:map<COperationNumber,T>, newDomain:set<OperationNumber>)
//   requires newDomain == set i | i in m :: AbstractifyCOperationNumberToOperationNumber(i)
//   ensures forall o :: o in newDomain ==> 0<=o<0x10000000000000000
//   ensures forall o :: o in newDomain ==> o as uint64 in m
// {
//   forall o | o in newDomain
//     ensures 0<=o<0x10000000000000000
//     ensures o as uint64 in m
//   {
//     var i :| i in m && o==AbstractifyCOperationNumberToOperationNumber(i);
//     assert 0 <= i as int < 0x10000000000000000;
//   }
// }

// function {:opaque} AbstractifyCVotesToVotes(votes:CVotes) : Votes
//   requires CVotesIsAbstractable(votes)
// {
//   // var newDomain := set i | i in votes.v :: AbstractifyCOperationNumberToOperationNumber(i);
//   lemma_AbstractifyMapOfThings(votes.v, set i | i in votes.v :: AbstractifyCOperationNumberToOperationNumber(i));
//   // map i | i in newDomain :: AbstractifyCVoteToVote(votes.v[COperationNumber(i as uint64)])
//   map j {:trigger votes.v[j as uint64]} | j in (set i | i in votes.v :: AbstractifyCOperationNumberToOperationNumber(i)) :: AbstractifyCVoteToVote(votes.v[j as uint64])
// }

// datatype CLearnerTuple = CLearnerTuple(received_2b_message_senders:set<EndPoint>, candidate_learned_value:CRequestBatch)

// function CLearnerTupleValid(c:CLearnerTuple) : bool
// {
//   true
// }

// predicate LearnerTupleIsAbstractable(tuple:CLearnerTuple)
// {
//   && SetOfEndPointsIsAbstractable(tuple.received_2b_message_senders)
//   && CRequestBatchIsAbstractable(tuple.candidate_learned_value)
// }

// function AbstractifyCLearnerTupleToLearnerTuple(tuple:CLearnerTuple) : LearnerTuple
//   ensures LearnerTupleIsAbstractable(tuple) ==> AbstractifyCLearnerTupleToLearnerTuple(tuple) == LearnerTuple(AbstractifyEndPointsToNodeIdentitiesSet(tuple.received_2b_message_senders), AbstractifyCRequestBatchToRequestBatch(tuple.candidate_learned_value))
// {
//   if (LearnerTupleIsAbstractable(tuple)) then 
//     var pkts := AbstractifyEndPointsToNodeIdentitiesSet(tuple.received_2b_message_senders);
//     var value := AbstractifyCRequestBatchToRequestBatch(tuple.candidate_learned_value);
//     LearnerTuple(pkts, value)
//   else 
//     var lt:LearnerTuple :| (true); lt
// }

// type CLearnerStateMap = map<COperationNumber, CLearnerTuple>

// predicate CLearnerTuplesAreAbstractable(tuples:map<COperationNumber,CLearnerTuple>)
// {
//   && (forall opn :: opn in tuples ==> LearnerTupleIsAbstractable(tuples[opn]))
// }

// predicate CLearnerTupleIsValid(tuple:CLearnerTuple) 
// {
//   // && SeqIsUnique(tuple.received_2b_message_senders)
//   && (forall i,j :: i in tuple.received_2b_message_senders && j in tuple.received_2b_message_senders ==> i != j)
//   && CRequestBatchValid(tuple.candidate_learned_value)
// }

// function {:opaque} AbstractifyCLearnerTuplesToLearnerTuples(m:map<COperationNumber,CLearnerTuple>) : map<OperationNumber,LearnerTuple>
//   requires CLearnerTuplesAreAbstractable(m)
//   ensures  var rm  := AbstractifyCLearnerTuplesToLearnerTuples(m);
//            forall k :: k in rm ==> (exists ck :: ck in m && AbstractifyCOperationNumberToOperationNumber(ck) == k)
// {
//   AbstractifyMap(m, AbstractifyCOperationNumberToOperationNumber, AbstractifyCLearnerTupleToLearnerTuple, RefineOperationNumberToCOperationNumber)
// }

// function method CBalLt(ba:CBallot, bb:CBallot) : bool
// {
//   || ba.seqno < bb.seqno
//   || (ba.seqno==bb.seqno && ba.proposer_id < bb.proposer_id)
// }

// function method CBalLeq(ba:CBallot, bb:CBallot) : bool
// {
//   || ba.seqno < bb.seqno
//   || (ba.seqno==bb.seqno && ba.proposer_id <= bb.proposer_id)
// }

// method CCBalLt(ba:CBallot, bb:CBallot) returns (b:bool)
//   // requires CBallotIsAbstractable(ba) && CBallotIsAbstractable(bb)
//   // ensures b == BalLt(AbstractifyCBallotToBallot(ba), AbstractifyCBallotToBallot(bb))
//   // ensures b == CCBalLt(ba, bb)
// {
//   if (ba.seqno < bb.seqno || (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)) {
//     b := true;
//   } else {
//     b := false;
//   }
// }

// predicate MapOfSeqNumsIsAbstractable(m:map<EndPoint,uint64>)
// {
//   forall e :: e in m ==> EndPointIsValidPublicKey(e)
// }

// function {:opaque} AbstractifyMapOfSeqNums(m:map<EndPoint,uint64>) : map<NodeIdentity,int>
//   requires MapOfSeqNumsIsAbstractable(m)
// {
//   lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
//   AbstractifyMap(m, AbstractifyEndPointToNodeIdentity, uint64_to_int, RefineNodeIdentityToEndPoint)
// }

}