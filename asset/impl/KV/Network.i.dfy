include ""


module Impl_SHT__Network_i 
{
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

	function AbstractifyCPacketToPacket(s: CPacket) : Packet 
		requires CPacketIsAbstractable(s)
	{
		Packet(AbstractifyEndPointToNodeIdentity(s.dst), AbstractifyEndPointToNodeIdentity(s.src), AbstractifyCPMsgToPMsg(s.msg))
	}
	type CNetwork = set<CPacket>

	predicate CNetworkIsAbstractable(s: CNetwork) 
	{
		(forall i :: i in s ==> CPacketIsAbstractable(i))
	}

	predicate CNetworkIsValid(s: CNetwork) 
	{
		CNetworkIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> CPacketIsValid(i))
	}

	function AbstractifyCNetworkToNetwork(s: CNetwork) : Network 
		requires CNetworkIsAbstractable(s)
	{
		AbstractifySet(s, AbstractifyCPacketToPacket)
	}

	function method CNetwork_Init() : CNetwork 
		ensures var n := CNetwork_Init(); CNetworkIsValid(n) && Network_Init(AbstractifyCNetworkToNetwork(n))
	{
		var t1 := 
			{}; 		
		t1
	}

	function method CPacketsTo(ps: set<CPacket>, dst: EndPoint) : set<CPacket> 
		requires (forall i :: i in ps ==> CPacketIsValid(i))
		requires EndPointIsValid(dst)
		ensures var lr := PacketsTo(AbstractifySet(ps, AbstractifyCPacketToPacket), AbstractifyEndPointToNodeIdentity(dst)); var cr := CPacketsTo(ps, dst); (forall i :: i in cr ==> CPacketIsValid(i)) && (AbstractifySet(cr, AbstractifyCPacketToPacket)) == (lr)
	{
		[Printer for . hasn't been implemented.]
	}

	function method CNetwork_Receive(n: CNetwork, dst: EndPoint) : set<CPacket> 
		requires CNetworkIsValid(n)
		requires EndPointIsValid(dst)
		ensures var recv := CNetwork_Receive(n, dst); (forall i :: i in recv ==> CPacketIsValid(i)) && Network_Receive(AbstractifyCNetworkToNetwork(n), AbstractifyEndPointToNodeIdentity(dst), AbstractifySet(recv, AbstractifyCPacketToPacket))
	{
		var t1 := 
			CPacketsTo(n, dst); 		
		t1
	}
}
