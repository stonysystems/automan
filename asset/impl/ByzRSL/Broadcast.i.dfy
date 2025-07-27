/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__Broadcast_i

[Action] LBroadcastToEveryone
Check passed
**********************************************************************/

include ""


module Impl_LiveByzRSL__Broadcast_i 
{

	function method CBroadcastToEveryone(c: CConfiguration, myidx: int, m: CMessage) : OutboundPackets 
		requires CConfigurationIsValid(c)
		requires CMessageIsValid(m)
		requires 0 <= myidx
		requires myidx < |c.replica_ids|
		ensures var sent_packets := CBroadcastToEveryone(c, myidx, m); OutboundPacketsIsValid(sent_packets) && LBroadcastToEveryone(AbstractifyCConfigurationToLConfiguration(c), myidx, AbstractifyCMessageToRslMessage(m), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			seq(|c.replica_ids|, (idx) => CPacket(c.replica_ids[idx], c.replica_ids[myidx], m)); 		
		t1
	}
}
