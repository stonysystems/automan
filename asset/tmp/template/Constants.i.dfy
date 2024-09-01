include "Configuration.i.dfy"
include "Parameters.i.dfy"

module Impl_LiveRSL__Constants_i {
 	import opened Impl_LiveRSL__Configuration_i
	import opened Impl_LiveRSL__Parameters_i

	datatype CConstants = 
	CConstants
	(
		config : CConfiguration ,
		params : CParameters
	)

	predicate CConstantsIsValid(
		s : CConstants)
		
	{
		CConstantsIsAbstractable(s)
		&&
		CConfigurationIsValid(s.config)
		&&
		CParametersIsValid(s.params)
	}

	predicate CConstantsIsAbstractable(
		s : CConstants)
		
	{
		CConfigurationIsAbstractable(s.config)
		&&
		CParametersIsAbstractable(s.params)
	}

	function AbstractifyCConstantsToLConstants(
		s : CConstants) : LConstants
		requires CConstantsIsAbstractable(s)
	{
		LConstants(AbstractifyCConfigurationToLConfiguration(s.config), AbstractifyCParametersToLParameters(s.params))
	}

	datatype CReplicaConstants = 
	CReplicaConstants
	(
		my_index : int ,
		all : CConstants
	)

	predicate CReplicaConstantsIsValid(
		s : CReplicaConstants)
		
	{
		CReplicaConstantsIsAbstractable(s)
		&&
		CConstantsIsValid(s.all)
	}

	predicate CReplicaConstantsIsAbstractable(
		s : CReplicaConstants)
		
	{
		CConstantsIsAbstractable(s.all)
	}

	function AbstractifyCReplicaConstantsToLReplicaConstants(
		s : CReplicaConstants) : LReplicaConstants
		requires CReplicaConstantsIsAbstractable(s)
	{
		LReplicaConstants(s.my_index, AbstractifyCConstantsToLConstants(s.all))
	}

	function method CReplicaConstantsValid(
		c : CReplicaConstants) : bool
		requires CReplicaConstantsIsValid(c)
		ensures var bc := CReplicaConstantsValid(c); var bl := LReplicaConstantsValid(AbstractifyCReplicaConstantsToLReplicaConstants(c)); (bl) == (bc)
	{
		0 <= c.my_index < |c.all.config.replica_ids|
	}
 
}
