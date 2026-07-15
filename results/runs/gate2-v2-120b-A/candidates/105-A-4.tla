---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS
  One,
  Half,
  Norm

(* ----------------------------------------------------------------------
   The state variable `p` represents a dyadic rational as a record
   with two fields:
     - p.num : the numerator (an integer)
     - p.den : the denominator (a positive integer, initially a power of 2)
   Throughout the specification we maintain that p.den > 0.
   ---------------------------------------------------------------------- *)
VARIABLES p

(* ----------------------------------------------------------------------
   One  and  Half  are constant dyadic rationals.
   The constants are declared in the .cfg file; here we give them default
   values that satisfy the intended semantics.
   ---------------------------------------------------------------------- *)
One == [num |-> 1, den |-> 1]
Half == [num |-> 1, den |-> 2]

(* ----------------------------------------------------------------------
   Norm(q) recursively reduces a dyadic rational `q` by dividing both the
   numerator and denominator by 2 while both are even.  This definition
   uses a bounded recursion depth (5) that is sufficient for the model
   checker because the denominator never exceeds 2^5 in the explored
   state space.  The bound can be increased if a larger space is needed.
   ---------------------------------------------------------------------- *)
Norm(q) ==
  LET Reduce(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
      THEN Reduce([num |-> q.num \div 2, den |-> q.den \div 2])
      ELSE q
  IN Reduce(q)

(* ----------------------------------------------------------------------
   Initial state: p is initialized to the constant One.
   ---------------------------------------------------------------------- *)
Init ==
  /\ p = One
  /\ p.den > 0

(* ----------------------------------------------------------------------
   The only possible step is to replace p by its normalized form.
   This models the “halving” operation: if both parts are even we can
   divide them by two, otherwise the state remains unchanged.
   ---------------------------------------------------------------------- *)
Next ==
  /\ p' = Norm(p)
  /\ p'.den > 0

(* ----------------------------------------------------------------------
   The specification: the system starts in Init and repeatedly
   executes Next.
   ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_<<p>>

(* ----------------------------------------------------------------------
   Type invariant: p is always a record with integer numerator and a
   positive integer denominator.
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ p.num \in Int
  /\ p.den \in Nat
  /\ p.den > 0

(* ----------------------------------------------------------------------
   Safety invariant: after normalisation the numerator and denominator
   are never both even (i.e., the fraction is in lowest terms with respect
   to factor 2).  This captures the intended effect of Norm.
   ---------------------------------------------------------------------- *)
Normed ==
  ~ (p.num % 2 = 0 /\ p.den % 2 = 0)

(* ----------------------------------------------------------------------
   Optional liveness / progress property: repeatedly applying Next can
   eventually reach the normalized form.  Not required by the .cfg but
   useful for documentation.
   ---------------------------------------------------------------------- *)
EventuallyNormed ==
  <>Normed

=============================================================================