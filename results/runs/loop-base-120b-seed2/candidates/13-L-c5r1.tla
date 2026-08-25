---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used by the model checker
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES choosing, number, cs

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ choosing \in [1..N -> BOOLEAN]
    /\ number   \in [1..N -> NatOverride]
    /\ cs       \in SUBSET 1..N

\* ----------------------------------------------------------------------
\* Initial state (same as the classic Bakery spec, but with Nat bounded)
\* ----------------------------------------------------------------------
Init ==
    /\ choosing = [i \in 1..N |-> FALSE]
    /\ number   = [i \in 1..N |-> 0]
    /\ cs       = {}

\* ----------------------------------------------------------------------
\* Helper: maximum ticket currently in use (0 if none)
\* ----------------------------------------------------------------------
MaxTicket ==
    IF \E j \in 1..N : number[j] # 0
    THEN Max({ number[j] : j \in 1..N })
    ELSE 0

\* ----------------------------------------------------------------------
\* Actions of the Bakery algorithm (combined for model‑checking convenience)
\* ----------------------------------------------------------------------
Request(i) ==
    /\ i \in 1..N
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ number'   = [number EXCEPT ![i] = (MaxTicket + 1) % (MaxNat + 1)]
    /\ UNCHANGED cs

Enter(i) ==
    /\ i \in 1..N
    /\ number[i] # 0
    /\ \A j \in 1..N :
          (j = i) \/ (number[j] = 0) \/
          ( (number[i] , i) < (number[j] , j) )
    /\ cs' = cs \cup {i}
    /\ UNCHANGED << choosing, number >>

Exit(i) ==
    /\ i \in 1..N
    /\ i \in cs
    /\ cs' = cs \setminus {i}
    /\ number' = [number EXCEPT ![i] = 0]
    /\ UNCHANGED choosing

Next ==
    \E i \in 1..N :
        \/ Request(i)
        \/ Enter(i)
        \/ Exit(i)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in cs : i = j

Inv == TypeOK /\ MutualExclusion

\* ----------------------------------------------------------------------
\* Specification (inductive: start from any TypeOK state)
\* ----------------------------------------------------------------------
vars == << choosing, number, cs >>

ISpec == TypeOK /\ [][Next]_vars

====