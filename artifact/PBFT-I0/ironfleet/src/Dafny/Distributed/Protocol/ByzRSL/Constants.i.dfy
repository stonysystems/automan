include "Configuration.i.dfy"
include "Parameters.i.dfy"

module LiveByzRSL__Constants_i {
import opened LiveByzRSL__Configuration_i
import opened LiveByzRSL__Parameters_i

datatype LConstants = LConstants(
  config:LConfiguration,
  params:LParameters
  )

datatype LReplicaConstants = LReplicaConstants(
  my_index:int,
  all:LConstants
  )

predicate LReplicaConstantsValid(c:LReplicaConstants)
{
  0 <= c.my_index < |c.all.config.replica_ids|
}

} 
