include "CConfiguration.i.dfy"


module LiveRSL__ConstantsState_i {
  import opened LiveRSL__Constants_i
  import opened LiveRSL__CPaxosConfiguration_i
  import opened LiveRSL__CTypes_i
  import opened LiveRSL__ParametersState_i
  import opened Native__NativeTypes_s
  import opened Native__Io_s
/************************** AutoMan Translation ************************/
  /** 5 + 0 */
  datatype CConstants = 
	CConstants(
		config: CConfiguration, 
		params: CParameters
	)

  /** 0 + 8 */
	predicate CConstantsIsValid(s: CConstants) 
	{
		CConstantsIsAbstractable(s) 
		&& 
		CConfigurationIsValid(s.config) 
		&& 
		CParametersIsValid(s.params)
	}

  /** 0 + 6 */
	predicate CConstantsIsAbstractable(s: CConstants) 
	{
		CConfigurationIsAbstractable(s.config) 
		&& 
		CParametersIsAbstractable(s.params)
	}

  /** 0 + 5 */
	function AbstractifyCConstantsToLConstants(s: CConstants) : LConstants 
		requires CConstantsIsAbstractable(s)
	{
		LConstants(AbstractifyCConfigurationToLConfiguration(s.config), AbstractifyCParametersToLParameters(s.params))
	}

  /** 5 + 0 */
  datatype CReplicaConstants = 
	CReplicaConstants(
		my_index: int, 
		all: CConstants
	)

  /** 0 + 6 + 1 */
	predicate CReplicaConstantsIsValid(s: CReplicaConstants) 
	{
		CReplicaConstantsIsAbstractable(s) 
		&& 
		CConstantsIsValid(s.all)
    && /* Manually added */
    0 <= s.my_index < |s.all.config.replica_ids|
	}

  /** 0 + 4 */
	predicate CReplicaConstantsIsAbstractable(s: CReplicaConstants) 
	{
		CConstantsIsAbstractable(s.all)
	}

  /** 0 + 5 */
	function AbstractifyCReplicaConstantsToLReplicaConstants(s: CReplicaConstants) : LReplicaConstants 
		requires CReplicaConstantsIsAbstractable(s)
	{
		LReplicaConstants(s.my_index, AbstractifyCConstantsToLConstants(s.all))
	}

  /** 6 + 2 */
  function method CReplicaConstantsValid(c: CReplicaConstants) : bool 
		requires CReplicaConstantsIsValid(c)
		ensures CReplicaConstantsValid(c) == LReplicaConstantsValid(AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		0 <= c.my_index 
		&& 
		c.my_index < |c.all.config.replica_ids|
	}
/************************** AutoMan Translation End ************************/

  /* manually added */
  method InitReplicaConstantsState(endPoint:EndPoint, config:CConfiguration) returns (rc:CReplicaConstants)
    requires CConfigurationIsValid(config)
    // requires PaxosEndPointIsValid(endPoint, config)
    requires endPoint in config.replica_ids  // To satisfy WFReplicaConstantsState
    ensures CReplicaConstantsIsValid(rc)
    ensures rc.all.config.replica_ids[rc.my_index] == endPoint
    ensures rc.all.config == config
    ensures rc.all.params.max_log_length > 0
    ensures rc.all.params.max_log_length < 10000
    ensures rc.all.params == StaticParams()
  {
    var params := StaticParams();
    //var config := CPaxosConfiguration(world.config.replica_ids);
    var constants := CConstants(config, params);
    var index := CGetReplicaIndex(endPoint, config);
    rc := CReplicaConstants(index, constants);
  }


}
