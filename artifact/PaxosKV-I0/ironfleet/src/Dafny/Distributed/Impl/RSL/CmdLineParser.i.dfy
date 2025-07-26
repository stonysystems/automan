include "../Common/CmdLineParser.i.dfy"
include "CConfiguration.i.dfy"

module PaxosCmdLineParser_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened CmdLineParser_i
import opened Common__NetClient_i
import opened LiveRSL__CPaxosConfiguration_i
import opened Common__SeqIsUniqueDef_i
import opened LiveRSL__Configuration_i
import opened Common__NodeIdentity_i

function paxos_config_parsing(args:seq<seq<byte>>) : CConfiguration
{
  var (_, endpoints) := parse_end_points(args);
  CConfiguration(endpoints)
}

function paxos_parse_id(arg:seq<byte>) : EndPoint
{
  var (_, ep) := parse_end_point(arg);
  ep
}

lemma lemma_MinQuorumSizeLessThanReplicaCount(config:CConfiguration)
  requires CConfigurationIsAbstractable(config)
  requires |config.replica_ids| > 0
  requires SeqIsUnique(config.replica_ids)
  ensures LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(config)) <= |config.replica_ids|
{
  assert |config.replica_ids| > 0;
  var h_config := AbstractifyCConfigurationToLConfiguration(config);
  lemma_AbstractifyEndPointsToNodeIdentities_properties(config.replica_ids);
  assert |h_config.replica_ids| == |config.replica_ids|;
  assert |h_config.replica_ids| > 0;
}

method parse_cmd_line(id:EndPoint, args:seq<seq<byte>>) returns (ok:bool, config:CConfiguration, my_index:int)
  requires EndPointIsValidPublicKey(id)
  ensures ok ==> && CConfigurationIsValid(config)
                && |config.replica_ids| > 0
                && 0 <= my_index as int < |config.replica_ids|
                && config == paxos_config_parsing(args)
                && config.replica_ids[my_index] == id
{
  var tuple1 := parse_end_points(args);
  ok := tuple1.0;
  if !ok {
    print "Error encountered while processing command-line arguments";
    return;
  }
  var endpoints := tuple1.1;

  if |endpoints| < 1 {
    print "Must have at least one replica.\n";
    ok := false;
    return;
  }

  if |endpoints| >= 0xffff_ffff_ffff_ffff {
  // if |endpoints| >= 100 {
    print "Internal error: impossibly many endpoints.\n";
    ok := false;
    return;
  }

  var unique := test_unique(endpoints);
  if !unique {
    print "Error: Each endpoint must be unique.\n";
    ok := false;
    return;
  }

  config := CConfiguration(endpoints);
  lemma_MinQuorumSizeLessThanReplicaCount(config);
  lemma_parse_cmd_line(config);

  if id in config.replica_ids
  {
    my_index := CGetReplicaIndex(id, config);
    return;
  } else {
    ok := false;
  }
  
  // if !ok {
  //   print "Error: Could not find local endpoint (last command-line endpoint) in list of preceding endpoints\n";
  //   return;
  // }
}

lemma {:axiom} lemma_parse_cmd_line(c:CConfiguration)
  ensures CConfigurationIsValid(c)

}
