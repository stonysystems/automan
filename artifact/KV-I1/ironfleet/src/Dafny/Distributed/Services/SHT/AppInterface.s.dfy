include "../../Common/Native/NativeTypes.s.dfy"

abstract module AppInterface_s {
    import opened Native__NativeTypes_s

    type Key(==, !new)
    type Value

    predicate method KeyLt(ka:Key, kb:Key) 

    lemma lemma_KeyOrdering()
        ensures forall k,k' :: KeyLt(k,k') ==> !KeyLt(k',k);                        // Antisymmetry
        ensures forall k,k' :: !KeyLt(k,k') ==> KeyLt(k',k) || k' == k;                        
        ensures forall k,k',k'' :: KeyLt(k,k') && KeyLt(k',k'') ==> KeyLt(k, k'');  // Transitivity

    function method KeyMin() : Key
        ensures forall k :: k == KeyMin() || KeyLt(KeyMin(), k);

    predicate ValidKey(key:Key)
    predicate ValidValue(v:Value)
    predicate KeyIsAbstractable(k:Key)
    predicate KeyIsValid(k:Key)
    predicate ValueIsAbstractable(v:Value)
    predicate ValueIsValid(v:Value)

    function AbstractifyKeyToKey(k:Key) : Key
    function RefineKeyToKey(k:Key) : Key
    function AbstractifyValueToValue(v:Value) : Value

    function MarshallSHTKey(k:Key) : seq<byte>
    function MarshallSHTValue(v:Value) : seq<byte>
}
