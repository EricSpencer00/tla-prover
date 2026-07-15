---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat, Nat

(* The natural number set is overridden to be the finite range 0..MaxNat *)
NatRange == 0 .. MaxNat

(* The theorem from the base specification that the double of any natural number is even. *)
DoubleIsEven == \A n \in NatRange : (2 * n) % 2 = 0

(* We declare the theorem as an assumption so that TLC can use it in the model. *)
ASSUME DoubleIsEven

(* No state variables are needed for this configuration module. *)

(* The main specification of the base module is assumed to be imported via an
   INSTANCE.  Since the base module is not provided here, we define a trivial stuttering
   specification that satisfies the assumptions. *)
VARIABLE dummy

Init == dummy = 0

Next == dummy' = dummy

Specification == Init /\ [][Next]_<<dummy>>

(* The required identifiers for the model configuration *)
SPECIFICATION == Specification
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

====