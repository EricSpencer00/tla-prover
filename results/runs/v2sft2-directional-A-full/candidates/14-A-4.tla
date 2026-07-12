---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, TLC

\* ========= CONSTANTS =========
CONSTANT N, MaxNat, Nat

\* ========= DEFINITIONS =========
\* The set of process identifiers
Proc == 1 .. N

\* The finite range of natural numbers used in this model (0..MaxNat-1)
FiniteNat == 0 .. MaxNat - 1

\* Ticket structure for each process
Ticket == [proc : Proc, n : FiniteNat]

\* State variables inherited from the Boulanger specification:
\*   - nextTicket: the next ticket number to be assigned
\*   - tickets: a mapping from each process to its current ticket
\*   - turn: the next process to be allowed into the critical section
VARIABLES nextTicket, tickets, turn

\* ========= INITIAL STATE =========
Init ==
    /\ nextTicket = 0
    /\ tickets = [p \in Proc |-> [proc |-> p, n |-> 0]]
    /\ turn = 1

\* ========= NEXT ACTION =========
\* Request phase: a process obtains a ticket
Request(p) ==
    /\ p \in Proc
    /\ nextTicket < FiniteNat
    /\ tickets' = [tickets EXCEPT ![p] = [proc |-> p, n |-> nextTicket]]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED turn

\* Grant phase: the process with the smallest ticket number becomes the turn
Grant ==
    /\ turn' = CHOOSE p \in Proc : tickets[p].n = Min(Set(tickets[p].n : p \in Proc))
    /\ UNCHANGED << nextTicket, tickets >>

\* The system alternates between request and grant actions
Next == \/ \E p \in Proc : Request(p)
        \/ Grant

\* ========= SPECIFICATION =========
Spec == Init /\ [][Next]_<<nextTicket, tickets, turn>>

\* ========= INVARIANTS =========
\* Mutual exclusion: at most one process can have the smallest ticket
MutualExclusion ==
    \A p, q \in Proc : (p # q) => tickets[p].n # tickets[q].n

\* Type correctness: all variables stay within their declared domains
TypeOK ==
    /\ nextTicket \in FiniteNat
    /\ tickets \in [Proc -> Ticket]
    /\ turn \in Proc
    /\ \A p \in Proc : tickets[p].proc = p
    /\ \A p \in Proc : tickets[p].n \in FiniteNat

\* Full inductive invariant (the original Boulanger invariant)
Inv ==
    /\ TypeOK
    /\ \A p, q \in Proc :
        (p # q) =>
          IF tickets[p].n < tickets[q].n THEN turn = p
          ELSE UNCHANGED turn

\* ========= STATE CONSTRAINT =========
StateConstraint ==
    \A p \in Proc : tickets[p].n < MaxNat

====