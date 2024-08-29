include ""


module Impl_LiveRSL__Parameters_i 
{

	datatype CParameters = 
	CParameters(
		max_log_length: int, 
		baseline_view_timeout_period: int, 
		heartbeat_period: int, 
		max_integer_val: CUpperBound, 
		max_batch_size: int, 
		max_batch_delay: int
	)

	predicate CParametersIsValid(s: CParameters) 
	{
		CParametersIsAbstractable(s) 
		&& 
		CUpperBoundIsValid(s.max_integer_val)
	}

	predicate CParametersIsAbstractable(s: CParameters) 
	{
		CUpperBoundIsAbstractable(s.max_integer_val)
	}

	function AbstractifyCParametersToLParameters(s: CParameters) : LParameters 
		requires CParametersIsAbstractable(s)
	{
		LParameters(s.max_log_length, s.baseline_view_timeout_period, s.heartbeat_period, AbstractifyCUpperBoundToUpperBound(s.max_integer_val), s.max_batch_size, s.max_batch_delay)
	}

	function method CWFLParameters(p: CParameters) : bool 
		requires CParametersIsValid(p)
		ensures CWFLParameters(p) == WFLParameters(AbstractifyCParametersToLParameters(p))
	{
		HOLDER
	}
}
