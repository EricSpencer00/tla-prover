---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat, Nat

(* 
  The constant Nat is overridden in the .cfg to be the finite set
  0..MaxNat.  MaxNat itself is a constant that the .cfg will assign.
*)

VARIABLE x

(* Initial state: choose any natural number x within Nat. *)
Init ==
    x \in Nat

(* Action: nondeterministically assign x to any value in Nat. 
   This models the trivial transition system where the only behavior
   is to stay within the bounded natural numbers. *)
Step ==
    x' \in Nat

Next ==
    Step

(* The specification combines the initial predicate and the
   temporal next-state relation. *)
Spec ==
    Init /\ [][Next]_<<x>>

(* Safety invariant: the double of any natural number is even. *)
EvenDouble ==
    x * 2 % 2 = 0

(* The theorem from the base specification is assumed as a constant-level
   assumption.  Since TLA+ does not have a direct "assume" construct, we
   expose it as a theorem that TLC will treat as a constant-level fact. *)
THEOREM DoubleIsEven ==
    \A n \in Nat: (n * 2) % 2 = 0

(* Export the required identifiers for the .cfg file. *)
SPECIFICATION Spec
INIT Init
NEXT Next
INVARIANT EvenDouble
THEOREM DoubleIsEven

====