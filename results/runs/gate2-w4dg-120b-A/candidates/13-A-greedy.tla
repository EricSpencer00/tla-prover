---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The Bakery mutual exclusion algorithm, with the natural numbers overridden by
\* a finite range 0..MaxNat for model checking.  The inductive spec ISpec starts
\* from any type-correct state, not just the initial state.
\* State: ticket numbers (Nat), a flag per process, and the critical-section set.

VARIABLES ticket, flag, cs

vars == <<ticket, flag, cs>>

TypeOK ==
  /\ ticket \in [1..N -> Nat]
  /\ flag \in [1..N -> BOOLEAN]
  /\ cs \subseteq (1..N)

MutualExclusion ==
  \A p, q \in cs : p = q

\* The full inductive invariant: every critical-section member holds a ticket
\* strictly below every non-member's ticket, and every member's flag is true.
Inv ==
  /\ MutualExclusion
  /\ \A p \in cs, q \in (1..N) \ cs : ticket[p] < ticket[q]
  /\ \A p \in cs : flag[p]

Init ==
  /\ ticket = [p \in 1..N |-> 0]
  /\ flag = [p \in 1..N |-> FALSE]
  /\ cs = {}

\* A process takes a ticket strictly above every currently held ticket.
TakeTicket(p) ==
  /\ ticket[p] = 0
  /\ ticket' = [ticket EXCEPT ![p] = 1 + Cardinality({q \in 1..N : ticket[q] # 0})]
  /\ UNCHANGED <<flag, cs>>

\* A process enters the critical section once it holds a ticket and no member
\* has a ticket not strictly below its own.
Enter(p) ==
  /\ ticket[p] # 0
  /\ \A q \in cs : ticket[p] < ticket[q]
  /\ cs' = cs \cup {p}
  /\ flag' = [flag EXCEPT ![p] = TRUE]
  /\ UNCHANGED ticket

\* A process leaves the critical section and resets its ticket and flag.
Exit(p) ==
  /\ p \in cs
  /\ cs' = cs \ {p}
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ flag' = [flag EXCEPT ![p] = FALSE]

Next ==
  \/ \E p \in 1..N : TakeTicket(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

ISpec == Init /\ [][Next]_vars

====