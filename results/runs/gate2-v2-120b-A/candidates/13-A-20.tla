---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat, Nat

\* Global finite range of natural numbers
Nat == 0 .. MaxNat

VARIABLES pc, ticket, chosen

\* State variable meanings:
\*   pc[p] ∈ {"idle", "wait", "cs"}   – program counter of process p
\*   ticket[p] ∈ Nat                  – ticket number of process p
\*   chosen[p] ∈ BOOLEAN              – indicates if p has picked a ticket

\* Convenience set of process identifiers
Proc == 1..N

\* Initial state: all processes idle, no tickets chosen
Init ==
    /\ pc = [p \in Proc |-> "idle"]
    /\ ticket = [p \in Proc |-> 0]
    /\ chosen = [p \in Proc |-> FALSE]

\* Action: a process p starts the entry protocol
Entry(p) ==
    /\ pc[p] = "idle"
    /\ chosen' = [chosen EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] = 
          IF MaxNat = 0 THEN 0
          ELSE 1 + Max({ ticket[q] : q \in Proc /\ chosen[q] })
      ]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED << >>

\* Action: a process p waits until it can enter the critical section
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \A q \in Proc :
          (q # p) => 
            (pc[q] # "cs" \/ 
             (ticket[p] < ticket[q]) \/ 
             (ticket[p] = ticket[q] /\ p < q))
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED << ticket, chosen >>

\* Action: a process p leaves the critical section
Exit(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ chosen' = [chosen EXCEPT ![p] = FALSE]
    /\ UNCHANGED ticket

\* The overall Next relation allows any process to take any of the three steps
Next ==
    \E p \in Proc : Entry(p) \/ Wait(p) \/ Exit(p)

\* The inductive specification: any reachable state must satisfy the invariant,
\* and the system evolves according to Next.
ISpec == Init /\ [][Next]_<<pc, ticket, chosen>>

\* Safety invariant: no two processes are simultaneously in the critical section
MutualExclusion ==
    \A p, q \in Proc :
        (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Type correctness invariant
TypeOK ==
    /\ pc \in [Proc -> {"idle", "wait", "cs"}]
    /\ ticket \in [Proc -> Nat]
    /\ chosen \in [Proc -> BOOLEAN]

\* Full inductive invariant (type correctness plus mutual exclusion)
Inv == MutualExclusion /\ TypeOK

=============================================================================