/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__CheckValSafety_i
**********************************************************************/

include ""


module Impl_LiveByzRSL__CheckValSafety_i 
{

	function method CConvert1bPacketsSeqToMsgSeq(S: OutboundPackets) : seq<CMessage> 
		requires OutboundPacketsIsValid(S)
		requires CSeqOfMessage1b(S)
		requires (forall p :: p in S ==> p.msg.CMessage_1b?)
		ensures |S| == |CConvert1bPacketsSeqToMsgSeq(S)|
		ensures (forall m :: m in CConvert1bPacketsSeqToMsgSeq(S) ==> m.CMessage_1b?)
		ensures var lr := Convert1bPacketsSeqToMsgSeq(AbstractifyOutboundCPacketsToSeqOfRslPackets(S)); var cr := CConvert1bPacketsSeqToMsgSeq(S); (forall i :: i in cr ==> CMessageIsValid(i)) && (AbstractifySeq(cr, AbstractifyCMessageToRslMessage)) == (lr)
	{
		if |S| == 0 then 
			[] 
		else 
			[S[0].msg] + CConvert1bPacketsSeqToMsgSeq(S[1 .. ])
	}

	function method CSeqOfMessage1b(S: OutboundPackets) : bool 
		requires OutboundPacketsIsValid(S)
		ensures var lr := LSeqOfMessage1b(AbstractifyOutboundCPacketsToSeqOfRslPackets(S)); var cr := CSeqOfMessage1b(S); (cr) == (lr)
	{
		(forall p :: p in S ==> p.msg.CMessage_1b?)
	}

	function method CSetOfMessage1bAboutBallot(S: OutboundPackets, b: CBallot) : bool 
		requires OutboundPacketsIsValid(S)
		requires CBallotIsValid(b)
		ensures var lr := LSetOfMessage1bAboutBallot(AbstractifyOutboundCPacketsToSeqOfRslPackets(S), AbstractifyCBallotToBallot(b)); var cr := CSetOfMessage1bAboutBallot(S, b); (cr) == (lr)
	{
		CSeqOfMessage1b(S) 
		&& 
		(forall p :: p in S ==> p.msg.bal_1b == b)
	}

	function method CAllAcceptorsHadNoProposal(S: OutboundPackets, opn: COperationNumber) : bool 
		requires OutboundPacketsIsValid(S)
		requires COperationNumberIsValid(opn)
		requires CSeqOfMessage1b(S)
		ensures var lr := LAllAcceptorsHadNoProposal(AbstractifyOutboundCPacketsToSeqOfRslPackets(S), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CAllAcceptorsHadNoProposal(S, opn); (cr) == (lr)
	{
		(forall p :: p in S ==> !(opn in p.msg.votes))
	}

	function method CCountInVotes(v: CRequestBatch, c: CBallot, opn: COperationNumber, S: OutboundPackets) : int 
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(c)
		requires COperationNumberIsValid(opn)
		requires OutboundPacketsIsValid(S)
		requires (forall p :: p in S ==> p.msg.CMessage_1b?)
		ensures CCountInVotes(v, c, opn, S) > 0 ==> (exists p :: p in S && opn in p.msg.votes && CBalLeq(c, p.msg.votes[opn].max_value_bal))
		ensures var lr := CountInVotes(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyOutboundCPacketsToSeqOfRslPackets(S)); var cr := CCountInVotes(v, c, opn, S); (cr) == (lr)
	{
		if |S| == 0 then 
			0 
		else 
			CCountInVotes(v, c, opn, S[1 .. ]) + if opn in S[0].msg.votes && CBalLeq(c, S[0].msg.votes[opn].max_value_bal) && S[0].msg.votes[opn].max_val == v then 1 else 0
	}

	function method CSetOfMessage1b(S: OutboundPackets) : bool 
		requires OutboundPacketsIsValid(S)
		ensures var lr := LSetOfMessage1b(AbstractifyOutboundCPacketsToSeqOfRslPackets(S)); var cr := CSetOfMessage1b(S); (cr) == (lr)
	{
		(forall p :: p in S ==> p.msg.CMessage_1b?)
	}

	function method Cmax_balInS(c: CBallot, S: OutboundPackets, opn: COperationNumber) : bool 
		requires CBallotIsValid(c)
		requires OutboundPacketsIsValid(S)
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
		ensures var lr := Lmax_balInS(AbstractifyCBallotToBallot(c), AbstractifyOutboundCPacketsToSeqOfRslPackets(S), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := Cmax_balInS(c, S, opn); (cr) == (lr)
	{
		(forall p :: p in S && opn in p.msg.votes ==> CBalLeq(p.msg.votes[opn].max_value_bal, c))
	}

	function method CExistsBallotInS(v: CRequestBatch, c: CBallot, S: OutboundPackets, opn: COperationNumber) : bool 
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(c)
		requires OutboundPacketsIsValid(S)
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
		ensures var lr := LExistsBallotInS(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifyOutboundCPacketsToSeqOfRslPackets(S), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CExistsBallotInS(v, c, S, opn); (cr) == (lr)
	{
		(exists p :: p in S && opn in p.msg.votes && p.msg.votes[opn].max_value_bal == c && p.msg.votes[opn].max_val == v)
	}

	function method CValIsHighestNumberedProposalAtBallot(v: CRequestBatch, c: CBallot, S: OutboundPackets, opn: COperationNumber) : bool 
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(c)
		requires OutboundPacketsIsValid(S)
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
		ensures var lr := LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifyOutboundCPacketsToSeqOfRslPackets(S), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CValIsHighestNumberedProposalAtBallot(v, c, S, opn); (cr) == (lr)
	{
		Cmax_balInS(c, S, opn) 
		&& 
		CExistsBallotInS(v, c, S, opn)
	}

	function method CAllVotesWithLargerBalHasSameValue(v: CRequestBatch, b: CBallot, p1bs: OutboundPackets, opn: COperationNumber) : bool 
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(b)
		requires OutboundPacketsIsValid(p1bs)
		requires COperationNumberIsValid(opn)
		requires (forall p :: p in p1bs ==> p.msg.CMessage_1b?)
		ensures var lr := AllVotesWithLargerBalHasSameValue(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(b), AbstractifyOutboundCPacketsToSeqOfRslPackets(p1bs), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CAllVotesWithLargerBalHasSameValue(v, b, p1bs, opn); (cr) == (lr)
	{
		(forall p :: p in p1bs && opn in p.msg.votes && CBalLeq(b, p.msg.votes[opn].max_value_bal) ==> p.msg.votes[opn].max_val == v)
	}

	function method CValIsSafeAt(v: CRequestBatch, p1bs: OutboundPackets, opn: COperationNumber, byzq: int, wq: int) : bool 
		requires CRequestBatchIsValid(v)
		requires OutboundPacketsIsValid(p1bs)
		requires COperationNumberIsValid(opn)
		requires (forall p :: p in p1bs ==> p.msg.CMessage_1b?)
		ensures var lr := LValIsSafeAt(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyOutboundCPacketsToSeqOfRslPackets(p1bs), AbstractifyCOperationNumberToOperationNumber(opn), byzq, wq); var cr := CValIsSafeAt(v, p1bs, opn, byzq, wq); (cr) == (lr)
	{
		(exists c :: CCountInVotes(v, c, opn, p1bs) >= wq && CAllVotesWithLargerBalHasSameValue(v, c, p1bs, opn))
	}
}
