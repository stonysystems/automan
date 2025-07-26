include "../../Protocol/ByzRSL/CheckValSafety.i.dfy"
include "CMessage.i.dfy"
include "CTypes.i.dfy"
include "../Common/GenericRefinement.i.dfy"

module LiveByzRSL__CheckValSafetyImpl_i {
import opened LiveByzRSL__CMessage_i
import opened LiveByzRSL__CTypes_i
import opened LiveByzRSL__CheckValSafety_i
import opened GenericRefinement_i

	/** 7 + 6 + 3  */
    function method CConvert1bPacketsSeqToMsgSeq(S: seq<CPacket>) : seq<CMessage> 
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires CSeqOfMessage1b(S)
		requires (forall p :: p in S ==> p.msg.CMessage_1b?)
		ensures |S| == |CConvert1bPacketsSeqToMsgSeq(S)|
		ensures (forall m :: m in CConvert1bPacketsSeqToMsgSeq(S) ==> m.CMessage_1b?)
		ensures var lr := Convert1bPacketsSeqToMsgSeq(AbstractifySeq(S, AbstractifyCPacketToRslPacket)); var cr := CConvert1bPacketsSeqToMsgSeq(S); (forall i :: i in cr ==> CMessageIsValid(i)) && (AbstractifySeq(cr, AbstractifyCMessageToRslMessage)) == (lr)
	{
		if |S| == 0 then 
			[] 
		else 
            /* manually add */
            reveal_Convert1bPacketsSeqToMsgSeq();
            assert CPacketIsValid(S[0]);
            assert CMessageIsValid(S[0].msg);
			[S[0].msg] + CConvert1bPacketsSeqToMsgSeq(S[1 .. ])
	}

	/** 4 + 2 */
    function method CSeqOfMessage1b(S: seq<CPacket>) : bool 
		requires (forall i :: i in S ==> CPacketIsValid(i))
		ensures var lr := LSeqOfMessage1b(AbstractifySeq(S, AbstractifyCPacketToRslPacket)); var cr := CSeqOfMessage1b(S); (cr) == (lr)
	{
		(forall p :: p in S ==> p.msg.CMessage_1b?)
	}

	/** 6 + 2 */
    function method CSetOfMessage1bAboutBallot(S: seq<CPacket>, b: CBallot) : bool
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires CBallotIsValid(b)
		ensures var lr := LSetOfMessage1bAboutBallot(AbstractifySeq(S, AbstractifyCPacketToRslPacket), AbstractifyCBallotToBallot(b)); var cr := CSetOfMessage1bAboutBallot(S, b); (cr) == (lr)
	{
		CSeqOfMessage1b(S) 
		&& 
		(forall p :: p in S ==> p.msg.bal_1b == b)
	}

	/** 4 + 4 */
    function method CAllAcceptorsHadNoProposal(S: seq<CPacket>, opn: COperationNumber) : bool 
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSeqOfMessage1b(S)
		ensures var lr := LAllAcceptorsHadNoProposal(AbstractifySeq(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CAllAcceptorsHadNoProposal(S, opn); (cr) == (lr)
	{
		(forall p :: p in S ==> !(opn in p.msg.votes))
	}

	/** 7 + 7 + 12 */
    function method CCountInVotes(v: CRequestBatch, c: CBallot, opn: COperationNumber, S: seq<CPacket>) : int 
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(c)
		requires COperationNumberIsValid(opn)
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires (forall p :: p in S ==> p.msg.CMessage_1b?)
		ensures CCountInVotes(v, c, opn, S) > 0 ==> (exists p :: p in S && opn in p.msg.votes && CBalLeq(c, p.msg.votes[opn].max_value_bal))
		ensures var lr := CountInVotes(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySeq(S, AbstractifyCPacketToRslPacket)); var cr := CCountInVotes(v, c, opn, S); (cr) == (lr)
	{
        /* manually add */
		ghost var ls := AbstractifySeq(S, AbstractifyCPacketToRslPacket);
		ghost var lv := AbstractifyCRequestBatchToRequestBatch(v);
        ghost var lopn := AbstractifyCOperationNumberToOperationNumber(opn);
        ghost var lc := AbstractifyCBallotToBallot(c);

		if |S| == 0 then 
			0 
		else 
            /* manually add */
			lemma_seq_sub(S, AbstractifyCPacketToRslPacket, 1, |S|);
			ghost var r_remain := CCountInVotes(v, c, opn, S[1..]);
			ghost var ls_remian := AbstractifySeq(S[1..], AbstractifyCPacketToRslPacket);
			ghost var lr_remian := CountInVotes(lv, lc, lopn, ls_remian);
			assert r_remain == lr_remian;
            ghost var cur := if opn in S[0].msg.votes && CBalLeq(c, S[0].msg.votes[opn].max_value_bal) && S[0].msg.votes[opn].max_val == v then 1 else 0;
			ghost var s_first := S[0];
			assert CPacketIsValid(s_first);
			CCountInVotes(v, c, opn, S[1 .. ]) + if opn in S[0].msg.votes && CBalLeq(c, S[0].msg.votes[opn].max_value_bal) && S[0].msg.votes[opn].max_val == v then 1 else 0
	}

	/** 4 + 2 */
    function method CSetOfMessage1b(S: seq<CPacket>) : bool 
		requires (forall i :: i in S ==> CPacketIsValid(i))
		ensures var lr := LSetOfMessage1b(AbstractifySeq(S, AbstractifyCPacketToRslPacket)); var cr := CSetOfMessage1b(S); (cr) == (lr)
	{
		(forall p :: p in S ==> p.msg.CMessage_1b?)
	}

	/** 4 + 5 */
    function method Cmax_balInS(c: CBallot, S: seq<CPacket>, opn: COperationNumber) : bool 
		requires CBallotIsValid(c)
		requires (forall i :: i in S ==> CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires CSetOfMessage1b(S)
		ensures var lr := Lmax_balInS(AbstractifyCBallotToBallot(c), AbstractifySeq(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := Cmax_balInS(c, S, opn); (cr) == (lr)
	{
		(forall p :: p in S && opn in p.msg.votes ==> CBalLeq(p.msg.votes[opn].max_value_bal, c))
	}

	/** 4 + 6 */
    function method CAllVotesWithLargerBalHasSameValue(v: CRequestBatch, b: CBallot, p1bs: seq<CPacket>, opn: COperationNumber) : bool 
		requires CRequestBatchIsValid(v)
		requires CBallotIsValid(b)
		requires (forall i :: i in p1bs ==> CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires (forall p :: p in p1bs ==> p.msg.CMessage_1b?)
		ensures var lr := AllVotesWithLargerBalHasSameValue(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(b), AbstractifySeq(p1bs, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); var cr := CAllVotesWithLargerBalHasSameValue(v, b, p1bs, opn); (cr) == (lr)
	{
		(forall p :: p in p1bs && opn in p.msg.votes && CBalLeq(b, p.msg.votes[opn].max_value_bal) ==> p.msg.votes[opn].max_val == v)
	}

	/** 4 + 5 */
    function method CValIsSafeAt(v: CRequestBatch, p1bs: seq<CPacket>, opn: COperationNumber, byzq: int, wq: int) : bool 
		requires CRequestBatchIsValid(v)
		requires (forall i :: i in p1bs ==> CPacketIsValid(i))
		requires COperationNumberIsValid(opn)
		requires (forall p :: p in p1bs ==> p.msg.CMessage_1b?)
		ensures var lr := LValIsSafeAt(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySeq(p1bs, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn), byzq, wq); var cr := CValIsSafeAt(v, p1bs, opn, byzq, wq); (cr) == (lr)
	{
		(exists p :: p in p1bs && opn in p.msg.votes && CCountInVotes(v, p.msg.votes[opn].max_value_bal, opn, p1bs) >= wq && CAllVotesWithLargerBalHasSameValue(v, p.msg.votes[opn].max_value_bal, p1bs, opn))
	}
}