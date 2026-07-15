---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, TLC

CONSTANT N, MaxNat, Nat

\*-------------------------------------------------------------------------------
\* Derived sets
\*-------------------------------------------------------------------------------
Proc == 1 .. N
TicketRange == 0 .. MaxNat

\*-------------------------------------------------------------------------------
\* State variables (inherited from Boulanger)
\*-------------------------------------------------------------------------------
VARIABLES pc, ticket, nextTicket

\* pc[p]   : program counter of process p (one of the symbolic labels)
\* ticket[p]: ticket number of process p (Nat, but we will constrain it)
\* nextTicket: the next ticket number to be assigned (Nat)

\*-------------------------------------------------------------------------------
\* Initial state (inherits Boulanger's Init, but restricts tickets)
\*-------------------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "idle"]
    /\ ticket = [p \in Proc |-> 0]
    /\ nextTicket \in TicketRange
    /\ UNCHANGED Nat
    /\ STATE_CONSTRAINT

\*-------------------------------------------------------------------------------
\* Actions (inherit Boulanger's actions, renamed for readability)
\*-------------------------------------------------------------------------------
Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)
    /\ UNCHANGED <<pc, ticket, nextTicket>> \ {pc, ticket, nextTicket}
    /\ STATE_CONSTRAINT

Enter(p) ==
    /\ pc[p] = "wait"
    /\ \A q \in Proc :
          (ticket[q] # ticket[p]) \/ (pc[q] \in {"idle", "cs"} \/ (q < p))
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<ticket, nextTicket>>
    /\ STATE_CONSTRAINT

Exit(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<ticket, nextTicket>>
    /\ STATE_CONSTRAINT

Next ==
    \/ \E p \in Proc : Request(p)
    \/ \E p \in Proc : Enter(p)
    \/ \E p \in Proc : Exit(p)

\*-------------------------------------------------------------------------------
\* State constraint to keep tickets within bounds
\*-------------------------------------------------------------------------------
STATE_CONSTRAINT ==
    /\ nextTicket \in TicketRange
    /\ \A p \in Proc : ticket[p] \in TicketRange

\*-------------------------------------------------------------------------------
\* Full specification
\*-------------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket>>

\*-------------------------------------------------------------------------------
\* Safety properties
\*-------------------------------------------------------------------------------
MutualExclusion ==
    \A p, q \in Proc :
        (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

TypeOK ==
    /\ pc \in [Proc -> {"idle", "wait", "cs"}]
    /\ ticket \in [Proc -> TicketRange]
    /\ nextTicket \in TicketRange

\* The invariant from the original specification
Inv == MutualExclusion /\ TypeOK

\*-------------------------------------------------------------------------------
\* Theorem (optional, not required by the cfg but useful)
\*-------------------------------------------------------------------------------
THEOREM Spec => []Inv

====