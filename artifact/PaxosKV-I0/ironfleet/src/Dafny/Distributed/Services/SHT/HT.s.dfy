include "AppInterface.i.dfy"
include "../../Common/Collections/Maps2.s.dfy"

////////////////////////////////////////////////////////
//  High-level spec for SHT is simply a hash table
////////////////////////////////////////////////////////

module SHT__HT_s {

import opened Collections__Maps2_s
import opened AppInterface_i`Spec

datatype OptionalValue = ValuePresent(v:Value) | ValueAbsent()

predicate OptionalValueIsAbstractable(ov:OptionalValue)
{
  match ov 
    case ValuePresent(v) => ValueIsAbstractable(v)
    case ValueAbsent() => true
}

predicate OptionalValueIsValid(ov:OptionalValue)
{
  match ov 
    case ValuePresent(v) => ValueIsValid(v)
    case ValueAbsent() => true
}


type Hashtable = map<Key,Value>


predicate HashtableIsAbstractable(table:Hashtable)
{
  && (forall k :: k in table ==> KeyIsAbstractable(k) && ValueIsAbstractable(table[k]))
}

predicate HashtableIsValid(table:Hashtable)
{
  && HashtableIsAbstractable(table)
  && (forall k :: k in table ==> KeyIsValid(k) && ValueIsValid(table[k]))
}

predicate SpecInit(h:Hashtable)
{
    h == map []
}

predicate Set(h:Hashtable, h':Hashtable, k:Key, ov:OptionalValue)
{
    h' == if ov.ValuePresent? then
            h[k := ov.v]
          else
            mapremove(h, k)
}

predicate Get(h:Hashtable, h':Hashtable, k:Key, ov:OptionalValue)
{
       h' == h
    && ov == if k in h then ValuePresent(h[k]) else ValueAbsent()
}

}
