include "../Common/NodeIdentity.i.dfy"
include "Message.i.dfy"

module SHT__SingleMessage_i {
import opened Concrete_NodeIdentity_i`Spec
import opened SHT__Message_i

// A type to ensure each message is delivered exactly once
// Note that we send sequence numbers starting at 1

datatype SingleMessage = SingleMessage(seqno:nat, dst:NodeIdentity, m:Message) 
                           | Ack(ack_seqno:nat) // I got everything up to and including seqno
                           | InvalidMessage()

}
