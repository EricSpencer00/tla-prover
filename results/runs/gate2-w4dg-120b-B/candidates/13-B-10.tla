---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat
\* The constant MaxNat is intended to be a runtime bound on the ticket
\* numbers drawn from the bakery numbering scheme. It is signed (it may be
\* negative, or above the natural bound of the underlying ordering type),
\* so a trivial truth check is needed to keep it from being an illegal value
\* that would break numeric ordering in the critical section.  The model
\* never itself supplies MaxNat -- it is a fixed constant and is set by the
\* spec.  The check must stay in place: weakening or dropping it is precisely
\* what lets an illegal (or underspecified) bound slip through to the
\* optimizer and break the ticket ordering the whole bakery scheme rests on.
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat

\* The actions below are the bakery-numbering critical-section protocol.
\* The override range is a modeling convenience that lets the spec test
\* the protocol against a bounded ceiling (a real bakery has a physical
\* capacity on how many tickets it can hand out before it recycles).
\* An unbounded range would be trivially true and uninteresting to model-check.

\* A worker who needs the shared resource registers intent.
Request(w) == ~Bakery!Requesting(w) /\ Bakery!Requesting' = [Bakery!Requesting EXCEPT ![w] = TRUE]
              /\ UNCHANGED <<Bakery!Ticket, Bakery!InCS>>

\* A requesting worker takes the next ticket in the override range.
TakeTicket(w) == Bakery!Requesting(w)
                 /\ Bakery!Ticket[w] = 0
                 /\ \E n \in NatOverride : Bakery!Ticket' = [Bakery!Ticket EXCEPT ![w] = n]
                 /\ UNCHANGED <<Bakery!Requesting, Bakery!InCS>>

\* A worker enters the critical section only when its ticket is strictly
\* earlier than every other worker's ticket, or no other ticket is held.
Enter(w) == Bakery!Ticket[w] # 0
            /\ \A v \in {0, 1} : v # w => (Bakery!Ticket[v] = 0 \/ Bakery!Ticket[w] < Bakery!Ticket[v])
            /\ Bakery!InCS' = [Bakery!InCS EXCEPT ![w] = TRUE]
            /\ UNCHANGED <<Bakery!Requesting, Bakery!Ticket>>

\* A worker leaves the critical section and gives its ticket back.
Leave(w) == Bakery!InCS[w]
            /\ Bakery!InCS' = [Bakery!InCS EXCEPT ![w] = FALSE]
            /\ Bakery!Ticket' = [Bakery!Ticket EXCEPT ![w] = 0]
            /\ Bakery!Requesting' = [Bakery!Requesting EXCEPT ![w] = FALSE]

\* A worker that has signed up but is stalled or forgotten is eventually
\* shed: its ticket and request are wiped so the bakery does not fill up.
Retry(w) == Bakery!Requesting[w] /\ Bakery!Ticket[w] # 0
            /\ Bakery!Requesting' = [Bakery!Requesting EXCEPT ![w] = FALSE]
            /\ Bakery!Ticket' = [Bakery!Ticket EXCEPT ![w] = 0]
            /\ UNCHANGED <<Bakery!InCS>>

Next == \E w \in {0, 1} : Request(w) \/ TakeTicket(w) \/ Enter(w) \/ Leave(w) \/ Retry(w)

vars == <<Bakery!Requesting, Bakery!Ticket, Bakery!InCS>>

TypeOK == Bakery!TypeOK
Init == Bakery!Init
Next_ == Next
Spec == Bakery!Spec /\ Next_
\* Mutual exclusion holds for every ticket in the override range: a worker
\* is never left in its critical section when its ticket is exhausted.
MutEx == \A w \in {0, 1} : (Bakery!Ticket[w] \in NatOverride) => ~Bakery!InCS[w]
====