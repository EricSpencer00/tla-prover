---- MODULE MC_sums_even ----
EXTENDS Naturals

(*-----------------------------------------------------------------
  Finite bound for natural numbers used during model checking.
  This constant is supplied by the configuration file.
-----------------------------------------------------------------*)
CONSTANT MaxNat

(*-----------------------------------------------------------------
  Finite version of the natural numbers set for model checking.
  Replaces Nat from Naturals via the NatOverride operator.
-----------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: n is any natural number within the finite range *)
Init == n \in NatOverride

(* Next-state relation: increment n while staying within the bound, or stutter *)
Next ==
    \/ /\ n < MaxNat
       /\ n' = n + 1
    \/ /\ n' = n

(* Overall specification *)
Spec == Init /\ [][Next]_<<n>>

(* Definition of evenness using the finite NatOverride set *)
Even(m) == \E k \in NatOverride : m = 2 * k

(* State invariant: double of n is even *)
DoubleIsEven == Even(2 * n)

(*-----------------------------------------------------------------
  Exported names for the TLC configuration file.
-----------------------------------------------------------------*)
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == << DoubleIsEven >>
PROPERTIES == [] DoubleIsEven
====