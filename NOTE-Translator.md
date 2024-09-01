# Harmony check

**Assignments of the data update `s'.a == s.(... ...)` should be handled last.**

**If the same member is assigned twice in previous assignments, report an error.**
```
&& func(s'.x)
&& s'.x == a /* Error; s'.x has been assigned with func() before */
```

**If there's a data update assignment then**

1. Each member can have at most one data update assignment; otherwise, report an error.
```
&& s'.x == a.(b := 1)
&& s'.x == s.x.(b := 1) /* Error; */
```
2. If an assignment based on the output data itself, query the data tracker to replace it with an assignment made before.
```
&& func(s'.x)
&& s' == s.(x := s'.x) /* Replaced with s' == s.(x := func()) */
```
If the query result does not exist, skip this member.
```
&& s' == s.(x := 1, y := s'.y) /* The assigment of y is ignored */
```
3. Assignments made before the data update assignment will be ignored.
```
&& s'.x == 1 /* ignored */
&& s'.y == 2 /* ignored */
&& s' == s.(x := 1, y := 2)
```

# Skipped during translation
  * Includes
  * Import
  * Common.topdecl_modifier_t for TopDecl.t

# For refinement generation

Recursive definition for collections is not allowed such as
```
s : seq<seq<T>>
```
For such cases, make `seq<T>` an alias so that we have
```
s : seq<T2>
->
forall i :: i in s ==> T2IsValid(i);
```

Generic programming only supports three built-in types: map, seq, and set; because otherwise it's hard to determine whether the `X` in `X<T>` is an alias to seq/set or it's a user-defined generic instance.
