---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, MaxNat, Nat

\* Derive the set of process identifiers
Proc == 0 .. N-1

\* State variables (inherited from Boulanger)
VARIABLES pc, ticket

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
PCVals == {"idle", "request", "wait", "cs", "exit"}

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ ticket' = [ticket EXCEPT ![i] = ticket[i] + 1]
    /\ UNCHANGED << >>

Wait(i) ==
    /\ pc[i] = "request"
    /\ \A j \in Proc :
          (pc[j] # "cs") \/ (ticket[i] < ticket[j]) \/ (ticket[i] = ticket[j] /\ i < j)
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED ticket

Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED ticket

Next ==
    \E i \in Proc :
        Request(i) \/ Wait(i) \/ Exit(i)

\* ----------------------------------------------------------------------
\* Safety (invariants)
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
    /\ pc \in [Proc -> PCVals]
    /\ ticket \in [Proc -> Nat]

Inv == /\ MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* State constraint to enforce ticket numbers below MaxNat
\* ----------------------------------------------------------------------
StateConstraint ==
    \A i \in Proc : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket>> /\ StateConstraint

\* ----------------------------------------------------------------------
\* Declare the top-level specification and invariants for TLC
\* ----------------------------------------------------------------------
SPECIFICATION Spec

INVARIANTS MutualExclusion, TypeOK, Inv

====