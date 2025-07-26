include "../Common/NodeIdentity.i.dfy"
include "../../Protocol/SHT/SingleMessage.i.dfy"
include "CMessage.i.dfy"

module SHT__CSingleMessage_i {
import opened SHT__SingleMessage_i
import opened Common__NodeIdentity_i
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened SHT__CMessage_i

datatype CSingleMessage = CSingleMessage(seqno:nat, dst:EndPoint, m:CMessage)
                            | CAck(ack_seqno:nat)
                            | CInvalidMessage()

predicate CSingleMessageIsAbstractable(smsg:CSingleMessage)
{
    match smsg
        case CSingleMessage(seqno, dst, m) => EndPointIsAbstractable(dst) && CMessageIsAbstractable(m)
        case CAck(ack_seqno) => true
        case CInvalidMessage => true
}

predicate CSingleMessageIsValid(smsg:CSingleMessage)
{
    match smsg
        case CSingleMessage(seqno, dst, m) => EndPointIsValid(dst) && CMessageIsValid(m)
        case CAck(ack_seqno) => true
        case CInvalidMessage => true
}

// predicate CSingleMessageIsValid(smsg:CSingleMessage, params:CParameters)
// {
//     match smsg
//         case CSingleMessage(seqno, _, _) => seqno < params.max_seqno
//         case CAck(seqno) => seqno < params.max_seqno
//         case CInvalidMessage => false
// }

function AbstractifyCSingleMessageToSingleMessage(smsg:CSingleMessage) : SingleMessage
    requires CSingleMessageIsAbstractable(smsg);
{
    match smsg
        case CSingleMessage(seqno, dst, m) => 
            SingleMessage(seqno as int, AbstractifyEndPointToNodeIdentity(dst), AbstractifyCMessageToMessage(m))
        case CAck(seqno) => Ack(seqno as int)
        case CInvalidMessage => InvalidMessage()
}

}