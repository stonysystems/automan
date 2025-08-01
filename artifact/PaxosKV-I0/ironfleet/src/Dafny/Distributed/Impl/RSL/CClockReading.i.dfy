include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/RSL/ClockReading.i.dfy"

module LiveRSL__CClockReading_i {
import opened Native__NativeTypes_s
import opened LiveRSL__ClockReading_i

datatype CClockReading = CClockReading(t:int)

function AbstractifyCClockReadingToClockReading(cclock:CClockReading) : ClockReading
{
  ClockReading(cclock.t)
}

} 
