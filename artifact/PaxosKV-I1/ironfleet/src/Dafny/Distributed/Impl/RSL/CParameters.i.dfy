include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/RSL/Parameters.i.dfy"
include "../Common/UpperBound.i.dfy"

module LiveRSL__ParametersState_i {
import opened Native__NativeTypes_s
import opened LiveRSL__Parameters_i
import opened Common__UpperBound_i
import opened Common__UpperBound_s

/************************** AutoMan Translation ************************/
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
    /* Manually added */
    && s.max_log_length > 0
    && s.baseline_view_timeout_period > 0
    && s.heartbeat_period > 0
    && (s.max_integer_val.CUpperBoundFinite? ==> s.max_integer_val.n > s.max_log_length)
    && s.max_batch_size > 0
    && s.max_batch_delay >= 0
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

  /* Manually added */
  function method StaticParams() : CParameters
  {
    CParameters(1000,   // max log length
                1000,   // baseline view timeout period (1000 ms = 1 sec)
                30,     // heartbeat period (100 ms)
                        // 0x8000_0000_0000_0000 - 1,  // Max integer value:  2^63 - 1
                CUpperBoundInfinite,
                1,     // max_batch_size
                10)     // max_batch_delay (10 ms)
  }
/************************** AutoMan Translation End ************************/
} 
