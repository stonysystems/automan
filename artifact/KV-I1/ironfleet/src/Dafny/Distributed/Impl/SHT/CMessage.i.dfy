include "../../Protocol/SHT/Message.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Protocol/SHT/Network.i.dfy"
include "Parameters.i.dfy"
include "../../Common/Logic/Option.i.dfy"

module SHT__CMessage_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened SHT__Message_i
import opened Common__NodeIdentity_i
import opened SHT__Network_i
import opened Impl_Parameters_i
import opened Logic__Option_i
import opened AppInterface_i`Spec
import opened SHT__HT_s
import opened SHT__SingleMessage_i
import opened SHT__Keys_i
import opened GenericRefinement_i
// import opened AppInterface_i

/************************** AutoMan Translation ************************/
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
		case CSetRequest(k_setrequest, v_setrequest) => SetRequest(AbstractifyKeyToKey(s.k_setrequest), s.v_setrequest)
		case CReply(k_reply, v) => Reply(AbstractifyKeyToKey(s.k_reply), s.v)
		case CRedirect(k_redirect, id) => Redirect(AbstractifyKeyToKey(s.k_redirect), AbstractifyEndPointToNodeIdentity(s.id))
		case CShard(kr, recipient) => Shard(s.kr, AbstractifyEndPointToNodeIdentity(s.recipient))
		case CDelegate(range, h) => Delegate(s.range, s.h)

	}
/************************** AutoMan Translation End ************************/

// For now, we use the same keys and values the app's spec does
// Someday, we may want to introduce a split between the app's
// high-level view of keys and values, and its low-level implementation

// datatype CMessage =
//       CGetRequest(k_getrequest:Key)
//     | CSetRequest(k_setrequest:Key, v_setrequest:OptionalValue)
//     | CReply(k_reply:Key, v:OptionalValue)
//     | CRedirect(k_redirect:Key, id:EndPoint)
//     | CShard(kr:KeyRange, recipient:EndPoint)
//     | CDelegate(range:KeyRange, h:Hashtable)

// // datatype CSingleMessage = CSingleMessage(seqno:uint64, dst:EndPoint, m:CMessage) 
// //                         | CAck(ack_seqno:uint64) // I got everything up to and including seqno
// //                         | CInvalidMessage()

// // type CPMsg = CSingleMessage
// // datatype CPacket = CPacket(dst:EndPoint, src:EndPoint, msg:CPMsg)

// predicate CMessageIsAbstractable(cmsg:CMessage)
// {
//     match cmsg 
//         case CGetRequest(k) => KeyIsAbstractable(k)
//         case CSetRequest(k, v) => KeyIsAbstractable(k) && OptionalValueIsAbstractable(v)
//         case CReply(k, v) => KeyIsAbstractable(k) && OptionalValueIsAbstractable(v)
//         case CRedirect(k, id) => KeyIsAbstractable(k) && EndPointIsAbstractable(id)
//         case CShard(kr, recipient) => KeyRangeIsAbstractable(kr) && EndPointIsAbstractable(recipient)
//         case CDelegate(range, h) => KeyRangeIsAbstractable(range) && HashtableIsAbstractable(h)
// }

// predicate CMessageIsValid(cmsg:CMessage)
// {
//     && CMessageIsAbstractable(cmsg)
//     && match cmsg 
//         case CGetRequest(k) => KeyIsValid(k)
//         case CSetRequest(k, v) => KeyIsValid(k) && OptionalValueIsValid(v)
//         case CReply(k, v) => KeyIsValid(k) && OptionalValueIsValid(v)
//         case CRedirect(k, id) => KeyIsValid(k) && EndPointIsValid(id)
//         case CShard(kr, recipient) => KeyRangeIsValid(kr) && EndPointIsValid(recipient)
//         case CDelegate(range, h) => KeyRangeIsValid(range) && HashtableIsValid(h)

// }

// function AbstractifyCMessageToMessage(cmsg:CMessage) : Message
//     requires CMessageIsAbstractable(cmsg);
// {
//     match cmsg
//         case CGetRequest(k) => GetRequest(k)
//         case CSetRequest(k, v) => SetRequest(k, v)
//         case CReply(k, v) => Reply(k, v)
//         case CRedirect(k, id) => Redirect(k, AbstractifyEndPointToNodeIdentity(id))
//         case CShard(kr, recipient) => Shard(kr, AbstractifyEndPointToNodeIdentity(recipient))
//         case CDelegate(range, h) => Delegate(range, h)
// }

// predicate CSingleMessageIsAbstractable(smsg:CSingleMessage)
// {
//     match smsg
//         case CSingleMessage(seqno, dst, m) => EndPointIsAbstractable(dst) && CMessageIsAbstractable(m)
//         case CAck(_) => true
//         case CInvalidMessage => true
// }

// function AbstractifyCSingleMessageToSingleMessage(smsg:CSingleMessage) : SingleMessage
//     requires CSingleMessageIsAbstractable(smsg);
// {
//     match smsg
//         case CSingleMessage(seqno, dst, m) => 
//             SingleMessage(seqno as int, AbstractifyEndPointToNodeIdentity(dst), AbstractifyCMessageToRslMessage(m))
//         case CAck(seqno) => Ack(seqno as int)
//         case CInvalidMessage => InvalidMessage()
// }

// predicate CSingleMessageIsValid(smsg:CSingleMessage, params:CParameters)
// {
//     match smsg
//         case CSingleMessage(seqno, _, _) => seqno < params.max_seqno
//         case CAck(seqno) => seqno < params.max_seqno
//         case CInvalidMessage => false
// }

// predicate CSingleMessageSeqIsAbstractable(cs:seq<CSingleMessage>) 
// {
//     forall i :: 0 <= i < |cs| ==> CSingleMessageIsAbstractable(cs[i])
// }

// function AbstractifySeqOfCSingleMessageToSeqOfSingleMessage(cs:seq<CSingleMessage>) : seq<SingleMessage>
//     requires CSingleMessageSeqIsAbstractable(cs);                                          
// {
//     MapSeqToSeq(cs, AbstractifyCSingleMessageToSingleMessage)
// }

//////////////////////////////////////////////////////////////////////////////

// predicate CPacketIsAbstractable(cpacket:CPacket)
// {
//        EndPointIsAbstractable(cpacket.dst)
//     && EndPointIsAbstractable(cpacket.src)
//     && CSingleMessageIsAbstractable(cpacket.msg)
// }

// function AbstractifyCPacketToShtPacket(cpacket:CPacket) : Packet
//     requires CPacketIsAbstractable(cpacket);
// {
//     Packet(AbstractifyEndPointToNodeIdentity(cpacket.dst),
//            AbstractifyEndPointToNodeIdentity(cpacket.src),
//            AbstractifyCSingleMessageToSingleMessage(cpacket.msg))
// }

// predicate CPacketsIsAbstractable(cps:set<CPacket>)
// {
//     forall p :: p in cps ==> CPacketIsAbstractable(p)
// }

// function {:opaque} AbstractifyCPacketsToPackets(cps:set<CPacket>) : set<Packet>
//     requires CPacketsIsAbstractable(cps);
//     ensures forall p :: p in cps ==> AbstractifyCPacketToShtPacket(p) in AbstractifyCPacketsToPackets(cps);
// {
//     set p | p in cps :: AbstractifyCPacketToShtPacket(p)
// }

// predicate CPacketSeqIsAbstractable(cps:seq<CPacket>)
// {
//     forall p :: p in cps ==> CPacketIsAbstractable(p)
// }

// function {:opaque} AbstractifySeqOfCPacketsToSetOfShtPackets(cps:seq<CPacket>) : set<Packet>
//     requires CPacketSeqIsAbstractable(cps);
//     ensures forall p :: p in cps ==> AbstractifyCPacketToShtPacket(p) in AbstractifySeqOfCPacketsToSetOfShtPackets(cps);
// {
//     set p | p in cps :: AbstractifyCPacketToShtPacket(p)
// }



// function AbstractifyOptionCPacketToOptionShtPacket(cp:Option<CPacket>) : Option<Packet>
//     requires OptionCPacketIsAbstractable(cp);
// {
//     match cp {
//         case Some(p) => Some(AbstractifyCPacketToShtPacket(p))
//         case None => None()
//     }
// }
}
