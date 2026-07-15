---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N
Ticket == 0..MaxNat

\* ----------------------------------------------------------------------
\* State variables (same as in the original Boulanger specification)
\* ----------------------------------------------------------------------
VARIABLES pc, ticket, nextTicket

\* ----------------------------------------------------------------------
\* Type correctness predicate (used for the TypeOK invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"idle", "request", "wait", "cs"}]
    /\ ticket \in [Proc -> Ticket]
    /\ nextTicket \in Ticket

\* ----------------------------------------------------------------------
\* Initial state (identical to the original Boulanger spec, but respecting
\* the finite Nat range)
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ nextTicket = 0

\* ----------------------------------------------------------------------
\* Actions (identical to the original Boulanger spec)
\* ----------------------------------------------------------------------
Request(i) ==
    /\ i \in Proc
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)
    /\ UNCHANGED << >>

Wait(i) ==
    /\ i \in Proc
    /\ pc[i] = "request"
    /\ \A j \in Proc :
          (j # i) => (pc[j] # "cs" \/ ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << ticket, nextTicket >>

Release(i) ==
    /\ i \in Proc
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED << ticket, nextTicket >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in Proc : Request(i)
    \/ \E i \in Proc : Wait(i)
    \/ \E i \in Proc : Release(i)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Inv == TypeOK /\ MutualExclusion

\* ----------------------------------------------------------------------
\* State constraint to keep ticket numbers strictly below MaxNat
\* (prunes states where any ticket reaches the maximum)
\* ----------------------------------------------------------------------
StateConstraint ==
    \A i \in Proc : ticket[i] < MaxNat

=============================================================================