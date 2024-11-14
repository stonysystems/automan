/**********************************************************************
AUTOMAN LOG

[Module] SHT__SingleMessage_i
**********************************************************************/

include ""


module Impl_SHT__SingleMessage_i 
{

	datatype CSingleMessage = 
	CSingleMessage(
		seqno: nat, 
		dst: EndPoint, 
		m: CMessage
	)
	 | 
	CAck(
		ack_seqno: nat
	)
	 | 
	CInvalidMessage(
		
	)

	predicate CSingleMessageIsValid(s: CSingleMessage) 
	{
		match s
		case CSingleMessage(seqno, dst, m) => CSingleMessageIsAbstractable(s) && EndPointIsValid(s.dst) && CMessageIsValid(s.m)
		case CAck(ack_seqno) => CSingleMessageIsAbstractable(s)
		case CInvalidMessage() => CSingleMessageIsAbstractable(s)

	}

	predicate CSingleMessageIsAbstractable(s: CSingleMessage) 
	{
		match s
		case CSingleMessage(seqno, dst, m) => EndPointIsAbstractable(s.dst) && CMessageIsAbstractable(s.m)
		case CAck(ack_seqno) => true
		case CInvalidMessage() => true

	}

	function AbstractifyCSingleMessageToSingleMessage(s: CSingleMessage) : SingleMessage 
		requires CSingleMessageIsAbstractable(s)
	{
		match s
		case CSingleMessage(seqno, dst, m) => SingleMessage(s.seqno, AbstractifyEndPointToNodeIdentity(s.dst), AbstractifyCMessageToMessage(s.m))
		case CAck(ack_seqno) => Ack(s.ack_seqno)
		case CInvalidMessage() => InvalidMessage()

	}
}
