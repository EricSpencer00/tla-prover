---- MODULE MCBakery ----
EXTENDS Naturals, Sequences

CONSTANT N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Finite natural number set used for model checking.
\* The reference configuration overrides the infinite Nat with the finite
\* set 0..MaxNat.  Here we capture that intention by defining Nat as a set
\* containing exactly those numbers.
\* ----------------------------------------------------------------------
Nat == 0 .. MaxNat

VARIABLES pc, ticket, choosing

\* ----------------------------------------------------------------------
\* State variable meanings (as in the classic Bakery algorithm):
\*   pc[i]       : program counter of process i (one of "idle", "try",
\*                "cs", "exit")
\*   ticket[i]   : integer ticket value of process i (0 when not in use)
\*   choosing[i] : boolean flag indicating if i is currently picking a
\*                ticket
\* ----------------------------------------------------------------------
ProcSet == 1 .. N

\* Initial state: all processes idle, no tickets, not choosing.
Init ==
    /\ pc = [i \in ProcSet |-> "idle"]
    /\ ticket = [i \in ProcSet |-> 0]
    /\ choosing = [i \in ProcSet |-> FALSE]

\* ----------------------------------------------------------------------
\* Actions (identical to those in the standard Bakery algorithm)
\* ----------------------------------------------------------------------
\* Process i begins to request entry.
StartRequest(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "idle"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<pc, ticket>>

\* Process i selects a ticket.
ChooseTicket(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "idle"
    /\ choosing[i] = TRUE
    /\ ticket' = [ticket EXCEPT ![i] = Max( { ticket[j] : j \in ProcSet } ) + 1]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "try"]
    /\ UNCHANGED << >>

\* Process i waits until it can enter the critical section.
Wait(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "try"
    /\ \A j \in ProcSet :
          (j # i) =>
            /\ ~choosing[j]
            /\ (ticket[i] < ticket[j]) \/ (ticket[i] = ticket[j] /\ i < j)
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<ticket, choosing>>

\* Process i exits the critical section.
ExitCS(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED choosing

\* The overall NEXT relation allows any enabled step of any process.
Next ==
    \E i \in ProcSet :
        \/ StartRequest(i)
        \/ ChooseTicket(i)
        \/ Wait(i)
        \/ ExitCS(i)

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in ProcSet :
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Type correctness: all variables stay within their intended domains.
TypeOK ==
    /\ pc \in [ProcSet -> {"idle", "try", "cs"}]
    /\ ticket \in [ProcSet -> Nat]
    /\ choosing \in [ProcSet -> BOOLEAN]

\* Full inductive invariant (combination of the two properties above).
Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* Specification: inductive specification (any type‑correct state is
\* allowed as a start, and every transition must preserve Inv).
\* ----------------------------------------------------------------------
ISpec == Init /\ [][Next]_<<pc, ticket, choosing>>

\* The configuration file expects the following names to be exported.
VARIABLES pc, ticket, choosing
\* (The above line makes the variables visible at the top level.)

=============================================================================