---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers, FiniteSets

\*--------------------------------------------------------------------
\* Constants
\*--------------------------------------------------------------------
CONSTANT MaxNat
CONSTANT Nat

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLE n

\*--------------------------------------------------------------------
\* Derived definitions
\*--------------------------------------------------------------------
NatRange == 0 .. MaxNat

\*--------------------------------------------------------------------
\* Initialization (does NOT need to satisfy the theorem)
\*--------------------------------------------------------------------
Init == 
    /\ n \in NatRange

\*--------------------------------------------------------------------
\* Action: choose any value nondeterministically at each step
\*--------------------------------------------------------------------
Step == 
    /\ n' \in NatRange

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Step]_<<n>>

\*--------------------------------------------------------------------
\* Theorem from the base specification (assumed as a constant-level
\* assumption for model checking).  The theorem states that the double
\* of any natural number is even.  It is expressed as a boolean
\* expression that must hold for every state reachable in the model.
\*--------------------------------------------------------------------
Theorem == 
    \A m \in NatRange : 2 * m \in Even

\* The set of even natural numbers, defined for convenience.
Even == { e \in NatRange : \E k \in NatRange : e = 2 * k }

\*--------------------------------------------------------------------
\* Safety property (optional, but provided for completeness)
\*--------------------------------------------------------------------
DoubleIsEven == 2 * n \in Even

\*--------------------------------------------------------------------
\* Invariant (identical to the safety property)
\*--------------------------------------------------------------------
Safe == DoubleIsEven

\*--------------------------------------------------------------------
\* Property (mirrors the theorem for TLC)
\*--------------------------------------------------------------------
Prop == \A m \in NatRange : 2 * m \in Even

\*--------------------------------------------------------------------
\* Exported definitions required by the .cfg
\*--------------------------------------------------------------------
SPECIFICATION Spec
INIT Init
NEXT Step
INVARIANT Safe
PROPERTY Prop
THEOREM Theorem

====