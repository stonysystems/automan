include "../../Protocol/ByzRSL/Broadcast.i.dfy"
include "CConstants.i.dfy"
include "CMessage.i.dfy"
include "CConfiguration.i.dfy"

module Impl__LiveByzRSL__Broadcast_i {
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__Broadcast_i
  import opened LiveByzRSL__CConfiguration_i
  import opened LiveByzRSL__CMessage_i
  import opened LiveByzRSL__PacketParsing_i
  import opened LiveByzRSL__ConstantsState_i
  // import opened LiveByzRSL__CMessageRefinements_i

  function method {:opaque} BuildBroadcastToEveryone(config:CConfiguration, my_index:int, msg:CMessage) : CBroadcast
    requires CConfigurationIsValid(config)
    requires ReplicaIndexValid(my_index, config)
    requires CMessageIsAbstractable(msg)
    requires Marshallable(msg)
    ensures
      var broadcast := BuildBroadcastToEveryone(config, my_index, msg);
      && CBroadcastIsValid(broadcast)
      && CBroadcastIsAbstractable(broadcast)
      && OutboundPacketsHasCorrectSrc(Broadcast(broadcast), config.replica_ids[my_index])
      && LBroadcastToEveryone(AbstractifyCConfigurationToLConfiguration(config), my_index as int, AbstractifyCMessageToRslMessage(msg), AbstractifyCBroadcastToRlsPacketSeq(broadcast))
  {
    if my_index < |config.replica_ids| then
      CBroadcast(config.replica_ids[my_index], config.replica_ids, msg)
    else
      CBroadcastNop
  }

  // lemma {:axiom} lemma_CBroadcastIsValid(broadcast:CBroadcast)
  //   ensures CBroadcastIsValid(broadcast)

}
