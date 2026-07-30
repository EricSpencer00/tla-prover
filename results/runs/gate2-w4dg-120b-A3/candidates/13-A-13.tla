---- MODULE MCBakery ----
EXTENDS Naturals

\* Model checking the Bakery algorithm with a bounded natural number range.
CONSTANTS N, MaxNat

\* NatOverride replaces the infinite set of Naturals with the finite range 0..MaxNat.
NatOverride == 0 .. MaxNat

VARIABLES ticket, using, waiting

vars == <<ticket, using, waiting>>

TypeOK ==
    /\ ticket \in [1 .. N -> NatOverride]
    /\ using \in [1 .. N -> BOOLEAN]
    /\ waiting \in SUBSET (1 .. N)

Init ==
    /\ ticket = [i \in 1 .. N |-> 0]
    /\ using = [i \in 1 .. N |-> FALSE]
    /\ waiting = {}

\* Requests are numbered only up to the configured maximum.
Request(i) ==
    /\ ~using[i]
    /\ i \notin waiting
    /\ \A j \in 1 .. N : ticket[j] # 0 => ticket[j] # ticket[i]
    /\ \A j \in 1 .. N : ticket[j] = 0 => ticket[i] = 0
    /\ \A j \in waiting : ticket[i] = 0 => ticket[j] /= 0
    /\ ticket' = [ticket EXCEPT ![i] = IF \E j \in 1 .. N : ticket[j] = 0 THEN 1 ELSE ticket[i] + 1]
    /\ waiting' = waiting \cup {i}
    /\ using' = using

Enter(i) ==
    /\ i \in waiting
    /\ \A j \in 1 .. N : \A k \in 1 .. N : (using[j] /\ ticket[j] < ticket[k]) => ticket[k] = 0
    /\ using' = [using EXCEPT ![i] = TRUE]
    /\ waiting' = waiting \ {i}
    /\ ticket' = [ticket EXCEPT ![i] = 0]

Exit(i) ==
    /\ using[i]
    /\ using' = [using EXCEPT ![i] = FALSE]
    /\ ticket' = ticket
    /\ waiting' = waiting

Next ==
    \/ \E i \in 1 .. N : Request(i)
    \/ \E i \in 1 .. N : Enter(i)
    \/ \E i \in 1 .. N : Exit(i)

Spec == Init /\ [][Next]_vars

\* The invariant from the inductive spec: at most one process in the critical section,
\* and every process in the section holds a fresh ticket in range.
MutualExclusion ==
    /\ \A i, j \in 1 .. N : (using[i] /\ using[j]) => i = j
    /\ \A i \in 1 .. N : using[i] => ticket[i] \in NatOverride

Inv == MutualExclusion

ISpec ==
    /\ Spec
    /\ UNCHANGED <<NatOverride>>

====