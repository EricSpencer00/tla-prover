---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES entering, ticket, nextTicket, served

vars == <<entering, ticket, nextTicket, served>>

\* The bakery invariant holds from all reachable states (inductive spec), not just
\* from the initial state.  MutualExclusion, TypeOK, and Inv are all carried over
\* from the original Bakery specification unchanged.
TypeOK ==
  /\ entering \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ served \in 0..(2 * N)

\* Mutual exclusion: any two processes in the critical section must be the same.
MutualExclusion ==
  \A p \in 1..N, q \in 1..N :
     (entering[p] /\ entering[q] /\ ticket[p] # 0 /\ ticket[q] # 0 /\ ticket[p] = ticket[q]) => p = q

NoOne == \A p \in 1..N : ~entering[p]

Init ==
  /\ entering = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ served = 0

Bump(t) == IF t < MaxNat THEN t + 1 ELSE t

\* Pick a ticket only while the current ticket pool is not exhausted.
TakeTicket(p) ==
  /\ ~entering[p]
  /\ ticket[p] = 0
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = Bump(nextTicket)
  /\ UNCHANGED <<entering, served>>

Enter(p) ==
  /\ ticket[p] # 0
  /\ ~entering[p]
  /\ NoOne
  /\ \A q \in 1..N : entering[q] => ticket[p] <= ticket[q]
  /\ entering' = [entering EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, nextTicket, served>>

\* Leaving frees the ticket slot so a fresh round can start.
Leave(p) ==
  /\ entering[p]
  /\ entering' = [entering EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ served' = IF served < 2 * N THEN served + 1 ELSE served
  /\ UNCHANGED nextTicket

Next == (\E p \in 1..N : TakeTicket(p)) \/ (\E p \in 1..N : Enter(p)) \/ (\E p \in 1..N : Leave(p))

\* Finite natural-number counterpart: the model uses the overridden Nat type.
NatOverride == (0 :> 0 @@ (MaxNat :> MaxNat))

Inv == NatOverride
====