---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers, FiniteSets, TLC

(*--------------------------------------------------------------------
  Finite natural-number domain used for model checking.
--------------------------------------------------------------------*)
CONSTANT MaxNat
Nat == 0..MaxNat

(*--------------------------------------------------------------------
  State variable representing the current natural number.
--------------------------------------------------------------------*)
VARIABLE n

(*--------------------------------------------------------------------
  Derived definition for the double of a natural number.
--------------------------------------------------------------------*)
Double(n) == 2 * n

(*--------------------------------------------------------------------
  Initial state: start with zero.
--------------------------------------------------------------------*)
Init == n = 0

(*--------------------------------------------------------------------
  Transition: increment n by one while staying within Nat.
--------------------------------------------------------------------*)
Next == 
    \/ /\ n < MaxNat
       /\ n' = n + 1
    \/ /\ n = MaxNat
       /\ UNCHANGED n

(*--------------------------------------------------------------------
  Specification: infinite repetition of Init followed by Next steps.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<n>>

(*--------------------------------------------------------------------
  Safety invariant: the double of n is always even.
--------------------------------------------------------------------*)
EvenDouble == Double(n) % 2 = 0

(*--------------------------------------------------------------------
  Safety invariant: n always stays in the finite natural-number set.
--------------------------------------------------------------------*)
NInRange == n \in Nat

(*--------------------------------------------------------------------
  The set of invariants that TLC will check.
--------------------------------------------------------------------*)
Inv == EvenDouble /\ NInRange

(*--------------------------------------------------------------------
  The main property: the specification satisfies the invariants.
--------------------------------------------------------------------*)
SpecImpliesInv == Spec => []Inv

(*--------------------------------------------------------------------
  Explicitly expose the identifiers required by the .cfg file.
--------------------------------------------------------------------*)
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == Inv
PROPERTIES == SpecImpliesInv

(*--------------------------------------------------------------------
  The theorem from the base specification (assumed true for model
  checking).  We state it here as an ASSUME to match the description.
--------------------------------------------------------------------*)
ASSUME DoubleEven = \A m \in Nat: Double(m) % 2 = 0

====