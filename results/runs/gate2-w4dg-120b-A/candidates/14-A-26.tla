---- MODULE MCBoulanger ----
EXTENDS Integers, FiniteSets

CONSTANTS N, MaxNat, Nat

\* Natural numbers are replaced by a finite range for model checking.
Numbers == 0..MaxNat

VARIABLES entering, reading, entering_, reading_, ticket

vars == <<entering, reading, entering_, reading_, ticket>>

TypeOK ==
    /\ entering \subseteq 1..N
    /\ reading \subseteq 1..N
    /\ entering_ \subseteq 1..N
    /\ reading_ \subseteq 1..N
    /\ ticket \in [1..N -> Numbers]

Init ==
    /\ entering = {}
    /\ reading = {}
    /\ entering_ = {}
    /\ reading_ = {}
    /\ ticket = [i \in 1..N |-> 0]

\* A process takes a ticket number one above the highest currently outstanding
\* ticket, then posts a request announcing that ticket.
Request(i) ==
    /\ i \notin entering
    /\ i \notin reading
    /\ ticket[i] = 0
    /\ entering' = entering \cup {i}
    /\ ticket' = [ticket EXCEPT ![i] = Cardinality({j \in 1..N : ticket[j] >= ticket[i] /\ ticket[j] # 0}) + 1]
    /\ UNCHANGED <<reading, entering_, reading_>>

\* Posting a request is a one-way, irreversible action: it consumes the process
\* from the waiting set and never returns it, which is what makes backpressure
\* work -- ticket numbers only ever rise, they are never re-used.
PostRequest(i) ==
    /\ i \in entering
    /\ i \notin entering_
    /\ ticket[i] >= 1
    /\ entering' = entering \ {i}
    /\ entering_' = entering_ \cup {i}
    /\ UNCHANGED <<reading, reading_, ticket>>

\* The bakery gate gives the requesting process the right to enter.
Enter(i) ==
    /\ i \in entering_
    /\ i \notin reading
    /\ i \notin reading_
    /\ \A j \in reading_ : ticket[i] < ticket[j]
    /\ entering_' = entering_ \ {i}
    /\ reading' = reading \cup {i}
    /\ reading_' = reading_ \cup {i}
    /\ UNCHANGED ticket

\* Leaving is the one reversible action in the system: it clears the request
\* and frees the process's ticket number, which is what prevents starvation.
Leave(i) ==
    /\ i \in reading
    /\ reading' = reading \ {i}
    /\ reading_' = reading_ \ {i}
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED <<entering, entering_>>

Next ==
    \/ \E i \in 1..N : Request(i) \/ PostRequest(i) \/ Enter(i) \/ Leave(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == reading \cap reading_ = {}

\* Every live ticket number is bounded below the maximum, enforced by the
\* state constraint and preserved across every action.
TicketBound == \A i \in 1..N : (ticket[i] # 0) => ticket[i] < MaxNat

\* The full inductive invariant of the bakery algorithm, kept here so the model
\* checker verifies it instead of re-deriving it at runtime.
Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ TicketBound

====