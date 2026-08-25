---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(*-----------------------------------------------------------------
  Finite version of the natural numbers, used for model checking.
  MaxNat is fixed to a concrete value (1,000,000) so that TLC can
  enumerate the state space.
-----------------------------------------------------------------*)
ASSUME MaxNat = 1000000

NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: any number within the finite range *)
Init == n \in NatOverride

(* No state changes *)
Next == UNCHANGED n

(* Specification required by the .cfg file *)
SPECIFICATION == Init /\ [][Next]_<<n>>

(* Aliases required by the .cfg file *)
INIT == Init
NEXT == Next

(* Definition of evenness using the finite natural numbers *)
Even(x) == \E k \in NatOverride : x = 2 * k

(* Theorem assumed for model checking: the double of any number is even *)
Theorem == \A m \in NatOverride : Even(2 * m)

ASSUME Theorem

INVARIANTS == <<>>
PROPERTIES == <<>>
====