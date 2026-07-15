---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Constants required by the reference .cfg
\* ----------------------------------------------------------------------
CONSTANT MaxNat
CONSTANT Nat

\* The constant Nat is intended to represent the set of natural numbers
\* from 0 up to MaxNat (inclusive).  This definition satisfies the
\* description that the infinite natural-number set is overridden with a
\* finite range so that TLC can explore a bounded state space.
Nat == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLE n

\* ----------------------------------------------------------------------
\* Specification components required by the task
\* ----------------------------------------------------------------------
\* SATISFY THE LEGACY SPECIFICATION NAMING
Spec ==
    /\ Init
    /\ [][Next]_<<n>>

INIT ==
    /\ n \in Nat
    /\ n = 0

\* The action Next models a simple nondeterministic step that
\* chooses any natural number in the finite range Nat.  This captures
\* the idea that the model checker will explore all possible values of n
\* within the bounded domain, rather than evolving n according to some
\* deterministic rule.
Next ==
    /\ n' \in Nat

\* The theorem from the base proof is assumed as a constant-level
\* assumption.  In TLA+ we express it as an invariant named DoubleEven,
\* which states that the double of n is even.  TLC will check this
\* invariant for all reachable states.
DoubleEven ==
    2 * n \in Nat \cup {x \in Nat: x = 2 * y /\ y \in Nat}

\* ----------------------------------------------------------------------
\* Exported names required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INIT Init
NEXT Next
INVARIANT DoubleEven
PROPERTY DoubleEven

====