include "../../SHT/SingleDelivery.i.dfy"
include "../../SHT/Message.i.dfy"
include "../../../Common/Framework/Environment.s.dfy"

module LiveSHT__Environment_i {
import opened Concrete_NodeIdentity_i`Spec
import opened SHT__Message_i
import opened SHT__SingleMessage_i 
import opened SHT__SingleDelivery_i
import opened Environment_s

type LSHTEnvironment = LEnvironment<NodeIdentity, SingleMessage>
type LSHTPacket = LPacket<NodeIdentity, SingleMessage>
type LSHTIo = LIoOp<NodeIdentity, SingleMessage>

function ConcatenateSHTIos(s:seq<seq<LSHTIo>>) : seq<LSHTIo>
{
    if |s| == 0 then
        []
    else
        s[0] + ConcatenateSHTIos(s[1..])
}

} 
