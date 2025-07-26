include "CMessage.i.dfy"
include "CSingleMessage.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Protocol/SHT/Network.i.dfy"

module SHT__CNetwork_i {
import opened Concrete_NodeIdentity_i`Spec
import opened Common__NodeIdentity_i
import opened SHT__CSingleMessage_i
import opened SHT__CMessage_i
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened SHT__Network_i
import opened Logic__Option_i

/************************** AutoMan Translation ************************/
    type CPMsg = CSingleMessage

	predicate CPMsgIsAbstractable(s: CPMsg) 
	{
		CSingleMessageIsAbstractable(s)
	}

	predicate CPMsgIsValid(s: CPMsg) 
	{
		CPMsgIsAbstractable(s) 
		&& 
		CSingleMessageIsValid(s)
	}

	function AbstractifyCPMsgToPMsg(s: CPMsg) : PMsg 
		requires CPMsgIsAbstractable(s)
	{
		AbstractifyCSingleMessageToSingleMessage(s)
	}

    datatype CPacket = 
	CPacket(
		dst: EndPoint, 
		src: EndPoint, 
		msg: CPMsg
	)

	predicate CPacketIsValid(s: CPacket) 
	{
		CPacketIsAbstractable(s) 
		&& 
		EndPointIsValid(s.dst) 
		&& 
		EndPointIsValid(s.src) 
		&& 
		CPMsgIsValid(s.msg)
	}

	predicate CPacketIsAbstractable(s: CPacket) 
	{
		EndPointIsAbstractable(s.dst) 
		&& 
		EndPointIsAbstractable(s.src) 
		&& 
		CPMsgIsAbstractable(s.msg)
	}

	function AbstractifyCPacketToShtPacket(s: CPacket) : Packet 
		requires CPacketIsAbstractable(s)
	{
		Packet(AbstractifyEndPointToNodeIdentity(s.dst), AbstractifyEndPointToNodeIdentity(s.src), AbstractifyCPMsgToPMsg(s.msg))
	}

    type CNetwork = set<CPacket>

	// predicate CNetworkIsAbstractable(s: CNetwork) 
	// {
	// 	(forall i :: i in s ==> CPacketIsAbstractable(i))
	// }

	// predicate CNetworkIsValid(s: CNetwork) 
	// {
	// 	CNetworkIsAbstractable(s) 
	// 	&& 
	// 	(forall i :: i in s ==> CPacketIsValid(i))
	// }

	// function AbstractifyCNetworkToNetwork(s: CNetwork) : Network 
	// 	requires CNetworkIsAbstractable(s)
	// {
	// 	AbstractifySet(s, AbstractifyCPacketToPacket)
	// }

    // function method CNetwork_Init() : CNetwork 
	// 	ensures var n := CNetwork_Init(); CNetworkIsValid(n) && Network_Init(AbstractifyCNetworkToNetwork(n))
	// {
	// 	var t1 := 
	// 		{}; 		
	// 	t1
	// }

    // function method CPacketsTo(ps: set<CPacket>, dst: EndPoint) : set<CPacket> 
	// 	requires (forall i :: i in ps ==> CPacketIsValid(i))
	// 	requires EndPointIsValid(dst)
	// 	ensures var lr := PacketsTo(AbstractifySet(ps, AbstractifyCPacketToPacket), AbstractifyEndPointToNodeIdentity(dst)); var cr := CPacketsTo(ps, dst); (forall i :: i in cr ==> CPacketIsValid(i)) && (AbstractifySet(cr, AbstractifyCPacketToPacket)) == (lr)
	// {
	// 	set p | p in ps && p.dst ==dst
	// }

	// function method CNetwork_Receive(n: CNetwork, dst: EndPoint) : set<CPacket> 
	// 	requires CNetworkIsValid(n)
	// 	requires EndPointIsValid(dst)
	// 	ensures var recv := CNetwork_Receive(n, dst); (forall i :: i in recv ==> CPacketIsValid(i)) && Network_Receive(AbstractifyCNetworkToNetwork(n), AbstractifyEndPointToNodeIdentity(dst), AbstractifySet(recv, AbstractifyCPacketToPacket))
	// {
	// 	var t1 := 
	// 		CPacketsTo(n, dst); 		
	// 	t1
	// }

/************************** AutoMan Translation End ************************/
// type CPMsg = CSingleMessage

// predicate CPMsgIsAbstractable(cpm:CPMsg)
// {
//     && CSingleMessageIsAbstractable(cpm)
// }

// predicate CPMsgIsValid(cpm:CPMsg)
// {
//     && CSingleMessageIsValid(cpm)
// }

// function AbstractifyCPMsgToPMsg(cpm:CPMsg) : PMsg
//     requires CPMsgIsAbstractable(cpm)
// {
//     AbstractifyCSingleMessageToSingleMessage(cpm)
// }


// datatype CPacket = CPacket(dst:EndPoint, src:EndPoint, msg:CPMsg)

// predicate CPacketIsAbstractable(cpacket:CPacket)
// {
//     && EndPointIsAbstractable(cpacket.dst)
//     && EndPointIsAbstractable(cpacket.src)
//     && CSingleMessageIsAbstractable(cpacket.msg)
// }

// predicate CPacketIsValid(cpacket:CPacket)
// {
//     && EndPointIsValid(cpacket.dst)
//     && EndPointIsValid(cpacket.src)
//     && CSingleMessageIsValid(cpacket.msg)
// }

// function AbstractifyCPacketToShtPacket(cpacket:CPacket) : Packet
//     requires CPacketIsAbstractable(cpacket);
// {
//     Packet(AbstractifyEndPointToNodeIdentity(cpacket.dst),
//            AbstractifyEndPointToNodeIdentity(cpacket.src),
//            AbstractifyCSingleMessageToSingleMessage(cpacket.msg))
// }

// type CNetwork = set<CPacket>

predicate CNetwork_Init(n:CNetwork) {
    n == {}
}

function method CPacketsTo(ps:set<CPacket>, dst:EndPoint) : set<CPacket>
{
    set p | p in ps && p.dst ==dst
}

predicate CNetwork_Receive(n:CNetwork, dst:EndPoint, recv:set<CPacket>) {
    recv == CPacketsTo(n, dst)
}

predicate OptionCPacketIsAbstractable(cp:Option<CPacket>)
{
    match cp {
        case Some(p) => CPacketIsAbstractable(p)
        case None => true
    }
}

// function method CNetwork_Send(n:CNetwork, src:EndPoint, out:set<CPacket>) : CNetwork
// {
//        (forall p :: p in out ==> p.src == src)  // Jay rewired this to have OutboundPackets
//     && n' == n + out
// }
}