include ""


module Impl_SHT__Message_i 
{

	datatype CMessage = 
	CGetRequest(
		k_getrequest: Key
	)
	 | 
	CSetRequest(
		k_setrequest: Key, 
		v_setrequest: OptionalValue
	)
	 | 
	CReply(
		k_reply: Key, 
		v: OptionalValue
	)
	 | 
	CRedirect(
		k_redirect: Key, 
		id: EndPoint
	)
	 | 
	CShard(
		kr: KeyRange, 
		recipient: EndPoint
	)
	 | 
	CDelegate(
		range: KeyRange, 
		h: Hashtable
	)

	predicate CMessageIsValid(s: CMessage) 
	{
		match s
		case CGetRequest(k_getrequest) => CMessageIsAbstractable(s) && KeyIsValid(s.k_getrequest)
		case CSetRequest(k_setrequest, v_setrequest) => CMessageIsAbstractable(s) && KeyIsValid(s.k_setrequest) && OptionalValueIsValid(s.v_setrequest)
		case CReply(k_reply, v) => CMessageIsAbstractable(s) && KeyIsValid(s.k_reply) && OptionalValueIsValid(s.v)
		case CRedirect(k_redirect, id) => CMessageIsAbstractable(s) && KeyIsValid(s.k_redirect) && EndPointIsValid(s.id)
		case CShard(kr, recipient) => CMessageIsAbstractable(s) && KeyRangeIsValid(s.kr) && EndPointIsValid(s.recipient)
		case CDelegate(range, h) => CMessageIsAbstractable(s) && KeyRangeIsValid(s.range) && HashtableIsValid(s.h)

	}

	predicate CMessageIsAbstractable(s: CMessage) 
	{
		match s
		case CGetRequest(k_getrequest) => KeyIsAbstractable(s.k_getrequest)
		case CSetRequest(k_setrequest, v_setrequest) => KeyIsAbstractable(s.k_setrequest) && OptionalValueIsAbstractable(s.v_setrequest)
		case CReply(k_reply, v) => KeyIsAbstractable(s.k_reply) && OptionalValueIsAbstractable(s.v)
		case CRedirect(k_redirect, id) => KeyIsAbstractable(s.k_redirect) && EndPointIsAbstractable(s.id)
		case CShard(kr, recipient) => KeyRangeIsAbstractable(s.kr) && EndPointIsAbstractable(s.recipient)
		case CDelegate(range, h) => KeyRangeIsAbstractable(s.range) && HashtableIsAbstractable(s.h)

	}

	function AbstractifyCMessageToMessage(s: CMessage) : Message 
		requires CMessageIsAbstractable(s)
	{
		match s
		case CGetRequest(k_getrequest) => GetRequest(AbstractifyKeyToKey(s.k_getrequest))
		case CSetRequest(k_setrequest, v_setrequest) => SetRequest(AbstractifyKeyToKey(s.k_setrequest), AbstractifyOptionalValueToOptionalValue(s.v_setrequest))
		case CReply(k_reply, v) => Reply(AbstractifyKeyToKey(s.k_reply), AbstractifyOptionalValueToOptionalValue(s.v))
		case CRedirect(k_redirect, id) => Redirect(AbstractifyKeyToKey(s.k_redirect), AbstractifyEndPointToNodeIdentity(s.id))
		case CShard(kr, recipient) => Shard(AbstractifyKeyRangeToKeyRange(s.kr), AbstractifyEndPointToNodeIdentity(s.recipient))
		case CDelegate(range, h) => Delegate(AbstractifyKeyRangeToKeyRange(s.range), AbstractifyHashtableToHashtable(s.h))

	}
}
