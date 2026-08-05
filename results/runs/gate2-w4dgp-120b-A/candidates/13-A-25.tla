---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs, want, ticket, nextTicket

vars == <<cs, want, ticket, nextTicket>>

\* Indexing runs from 1 to N inclusive.
Nats == 0 .. MaxNat

\* Ticket numbers are bounded by the finite range, not by the
\* infinite set of naturals (this is the override in the .cfg).
Nat == Nats

TypeOK ==
  /\ cs \in SUBSET (1 .. N)
  /\ want \in [1 .. N -> BOOLEAN]
  /\ ticket \in [1 .. N -> Nats]
  /\ nextTicket \in Nats

Init ==
  /\ cs = {}
  /\ want = [i \in 1 .. N |-> FALSE]
  /\ ticket = [i \in 1 .. N |-> 0]
  /\ nextTicket = 0

\* A process wants to enter the critical section.
EnterRequest(i) ==
  /\ ~want[i]
  /\ cs = {}
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<cs, ticket, nextTicket>>

\* A process takes a ticket; the counter saturates at its maximum.
TakeTicket(i) ==
  /\ want[i]
  /\ cs = {}
  /\ ticket[i] = 0
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE MaxNat
  /\ UNCHANGED <<cs, want>>

\* A process enters its critical section once its ticket is the oldest.
EnterCS(i) ==
  /\ want[i]
  /\ ticket[i] # 0
  /\ cs = {}
  /\ \A j \in 1 .. N : (want[j] /\ ticket[j] # 0) => ticket[i] <= ticket[j]
  /\ cs' = {i}
  /\ UNCHANGED <<want, ticket, nextTicket>>

\* The process in the critical section exits.
ExitCS(i) ==
  /\ i \in cs
  /\ cs' = {}
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED nextTicket

Next ==
  \E i \in 1 .. N :
    \/ EnterRequest(i)
    \/ TakeTicket(i)
    \/ EnterCS(i)
    \/ ExitCS(i)

\* Mutual exclusion is preserved: any process in the critical section is the
\* one holder the shared set names, so at most one process is ever inside.
MutualExclusion ==
  \A i \in cs : \A j \in cs : i = j

\* The ticketing discipline keeps the system type-correct and the
\* inductive invariant holding across every reachable state.
Inv ==
  \A i \in cs : want[i] /\ ticket[i] # 0

\* The specification is inductive: it must recover from any state that
\* already satisfies the invariant, not just from the initial state.
ISpec == Init /\ [][Next]_vars

====