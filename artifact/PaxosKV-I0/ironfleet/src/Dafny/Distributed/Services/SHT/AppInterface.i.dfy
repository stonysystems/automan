include "AppInterface.s.dfy"
include "Bytes.s.dfy"

module AppInterface_i refines AppInterface_s {
import opened Bytes_s
export Spec
    provides Native__NativeTypes_s
    reveals Key // provides Key REVIEW: triggers a Dafny bug
    provides Value
    provides KeyLt
    provides lemma_KeyOrdering
    provides KeyMin, ValidKey, ValidValue, MarshallSHTKey, MarshallSHTValue
    provides KeyIsAbstractable, KeyIsValid, ValueIsAbstractable, ValueIsValid, AbstractifyKeyToKey, AbstractifyValueToValue, RefineKeyToKey
export All reveals *


type Key(==, !new) = uint64
type Value = seq<byte>

predicate KeyIsAbstractable(k:Key)
{
    true
}

predicate method KeyIsValid(k:Key)
{
    true
}

function  AbstractifyKeyToKey(k:Key) : Key
{
    k
}

function RefineKeyToKey(k:Key) : Key
{
    k
}

predicate ValueIsAbstractable(v:Value)
{
    true
}

predicate method ValueIsValid(v:Value)
{
    |v| <= max_val_len()
}


predicate method KeyLt(ka:Key, kb:Key) 
{
    ka < kb 
}

function AbstractifyValueToValue(v:Value) : Value
{
    v
}

lemma lemma_KeyOrdering()
{
}

function method max_key_len() : int { 16 }  
function method max_val_len() : int { 8192 }  

predicate method ValidKey(key:Key)
{
    true 
}

predicate method ValidValue(v:Value)
{
    |v| <= max_val_len()
}

function method KeyMin() : Key { 0 }

function MarshallSHTKey(k:Key) : seq<byte>
{
    Uint64ToBytes(k)
}

function MarshallSHTValue(v:Value) : seq<byte>
{
    if |v| < 0x1_0000_0000_0000_0000 then
        Uint64ToBytes(|v| as uint64) + v
    else
        []  // We only handle reasonably sized values
}


// type Key(==, !new) = uint64
// type Value = seq<byte>

// predicate method KeyLt(ka:Key, kb:Key) 
// {
//     ka < kb 
// }

// lemma lemma_KeyOrdering()
// {
// }

// function max_key_len() : int { 16 }  
// function max_val_len() : int { 1024 }  

// predicate ValidKey(key:Key)
// {
//     true 
// }

// predicate ValidValue(v:Value)
// {
//     |v| < max_val_len()
// }

// function method KeyMin() : Key { 0 }

// function MarshallSHTKey(k:Key) : seq<byte>
// {
//     Uint64ToBytes(k)
// }

// function MarshallSHTValue(v:Value) : seq<byte>
// {
//     if |v| < 0x1_0000_0000_0000_0000 then
//         Uint64ToBytes(|v| as uint64) + v
//     else
//         []  // We only handle reasonably sized values
// }
}
