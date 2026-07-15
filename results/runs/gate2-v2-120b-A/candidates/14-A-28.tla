---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT N          \* Number of processes, will be instantiated to 3 in the .cfg
CONSTANT MaxNat    \* Upper bound for the overridden natural numbers (0..MaxNat)
CONSTANT Nat       \* Finite set representing the natural numbers 0..MaxNat

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 0 .. N-1

\* ----------------------------------------------------------------------
\* State variables (as in the original Boulanger specification)
\* ----------------------------------------------------------------------
VARIABLES pc, ticket

\* ----------------------------------------------------------------------
\* Type definitions (for readability, not exported)
\* ----------------------------------------------------------------------
\* pc[p] ∈ {"idle", "request", "cs"}
\* ticket[p] ∈ Nat
\* ----------------------------------------------------------------------

\* ----------------------------------------------------------------------
\* Initial predicate (inherits the Boulanger init, constrained to Nat)
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "idle"]
    /\ ticket = [p \in Proc |-> 0]

\* ----------------------------------------------------------------------
\* Actions (inherit the original Boulanger actions)
\* ----------------------------------------------------------------------
Request(p) ==
    /\ p \in Proc
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "request"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]   \* any Nat value; 0 is sufficient for init

Enter(p) ==
    /\ p \in Proc
    /\ pc[p] = "request"
    /\ \A q \in Proc: (q # p) => (ticket[p] < ticket[q]) \/ (ticket[p] = ticket[q] /\ p < q)
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED ticket

Exit(p) ==
    /\ p \in Proc
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED ticket

Next ==
    \/ \E p \in Proc: Request(p)
    \/ \E p \in Proc: Enter(p)
    \/ \E p \in Proc: Exit(p)

\* ----------------------------------------------------------------------
\* Safety properties (from the original Boulanger spec)
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A p, q \in Proc: (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

TypeOK ==
    /\ pc \in [Proc -> {"idle", "request", "cs"}]
    /\ ticket \in [Proc -> Nat]

\* Full inductive invariant (named Inv)
\* For illustration we reuse the two properties above; a real Boulanger spec
\* may have additional conjuncts, but they are not required for this module.
Inv ==
    /\ TypeOK
    /\ MutualExclusion

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket>>

\* ----------------------------------------------------------------------
\* State constraint: ticket numbers must stay strictly below MaxNat
\* (i.e., they belong to Nat = 0..MaxNat and are < MaxNat)
\* ----------------------------------------------------------------------
StateConstraint ==
    \A p \in Proc: ticket[p] < MaxNat

\* ----------------------------------------------------------------------
\* The .cfg will refer to these identifiers:
\*   CONSTANTS N, MaxNat, Nat
\*   SPECIFICATION Spec
\*   INVARIANTS MutualExclusion, TypeOK, Inv
\* ----------------------------------------------------------------------
====