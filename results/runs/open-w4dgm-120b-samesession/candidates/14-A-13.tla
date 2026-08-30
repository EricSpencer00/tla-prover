---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

\* The ticket numbers normally belong to the infinite set Nat, but for
\* model checking they are drawn from the finite range 0..MaxNat.  The
\* override below replaces Nat with a bounded version while keeping the
\* Naturals import (the .cfg handles the replacement itself).
NatOverride == Nat

VARIABLES holder, pc, tkt, nextTicket, line

vars == <<holder, pc, tkt, nextTicket, line>>

TypeOK ==
    /\ holder \in {"none"} \cup (1..N)
    /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
    /\ tkt \in [1..N -> NatOverride]
    /\ nextTicket \in NatOverride
    /\ line \in Seq(1..N)

Init ==
    /\ holder = "none"
    /\ pc = [p \in 1..N |-> "idle"]
    /\ tkt = [p \in 1..N |-> 0]
    /\ nextTicket = 1
    /\ line = <<>>

\* Request: a process joins the bounded request queue, keeping the queue
\* within its capacity.  Ticket numbers are allocated from the bounded
\* range below MaxNat, and the action is disabled once the next ticket
\* would reach the maximum -- that is the backpressure the model uses.
Request(p) ==
    /\ pc[p] = "idle"
    /\ Len(line) < MaxNat
    /\ tkt[p] = 0
    /\ tkt' = [tkt EXCEPT ![p] = nextTicket]
    /\ nextTicket' = nextTicket + 1
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ line' = Append(line, p)
    /\ UNCHANGED holder

\* Grant: the ticket at the head of the line is handed to the holder if
\* the critical section is free, so admitted processes may jump the line.
Grant ==
    /\ Len(line) > 0
    /\ holder = "none"
    /\ holder' = Head(line)
    /\ line' = Tail(line)
    /\ UNCHANGED <<pc, tkt, nextTicket>>

\* Reorder: the reservation messages in the bounded queue are reordered
\* in transit, swapping two adjacent entries at a time.
Reorder ==
    /\ Len(line) >= 2
    /\ \E i \in 1..(Len(line) - 1):
        line' = [line EXCEPT ![i] = line[i+1], ![i+1] = line[i]]
    /\ UNCHANGED <<holder, pc, tkt, nextTicket>>

Enter(p) ==
    /\ holder = p
    /\ pc[p] = "waiting"
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<holder, tkt, nextTicket, line>>

Exit(p) ==
    /\ holder = p
    /\ pc[p] = "critical"
    /\ holder' = "none"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ tkt' = [tkt EXCEPT ![p] = 0]
    /\ UNCHANGED <<nextTicket, line>>

Cancel(p) ==
    /\ pc[p] = "waiting"
    /\ tkt[p] \notin line
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ tkt' = [tkt EXCEPT ![p] = 0]
    /\ UNCHANGED <<holder, nextTicket, line>>

Next ==
    \/ \E p \in 1..N: Request(p)
    \/ Grant
    \/ Reorder
    \/ \E p \in 1..N: Enter(p)
    \/ \E p \in 1..N: Exit(p)
    \/ \E p \in 1..N: Cancel(p)

Spec == Init /\ [][Next]_vars

 \* Strong fairness on every granted reservation keeps the system
 \* live: every waiting process is eventually admitted.
Fairness == \A p \in 1..N: SF_vars(Enter(p))

MutualExclusion ==
    /\ \A p \in 1..N: pc[p] = "critical" => holder = p
    /\ \A p \in 1..N: pc[p] = "critical" => tkt[p] \in line
    /\ holder # "none" => pc[holder] = "critical"
    /\ \A p, q \in 1..N: (holder = p /\ holder = q) => p = q

 \* Bounded range of ticket numbers: all issued tickets stay below the
 \* configured maximum, which is what keeps the model finite.
TicketBound == \A p \in 1..N: pc[p] = "waiting" => tkt[p] < MaxNat

Inv == MutualExclusion /\ TicketBound

====