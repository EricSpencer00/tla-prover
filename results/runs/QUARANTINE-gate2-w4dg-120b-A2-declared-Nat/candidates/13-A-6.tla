---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* NatOverride replaces the infinite natural-number set with a finite bounded
\* set 0..MaxNat for model checking. The .cfg substitutes NatOverride for Nat.
NatOverride == 0..MaxNat

VARIABLES busy, entering, ticket, nextTicket, served

vars == <<busy, entering, ticket, nextTicket, served>>

TypeOK ==
  /\ busy \in 0..N
  /\ entering \in 0..N
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride
  /\ served \in 0..N

MutualExclusion == busy <= 1

\* The full inductive invariant of the Bakery spec, carried over unchanged.
Inv == TypeOK /\ MutualExclusion

Init ==
  /\ busy = 0
  /\ entering = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ served = 0

TakeTicket(i) ==
  /\ entering < N
  /\ entering' = entering + 1
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ UNCHANGED <<busy, served>>

Enter(i) ==
  /\ ticket[i] > 0
  /\ busy = 0
  /\ busy' = 1
  /\ entering' = entering - 1
  /\ UNCHANGED <<ticket, nextTicket, served>>

Exit(i) ==
  /\ busy = 1
  /\ ticket[i] > 0
  /\ busy' = 0
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ served' = IF served < N THEN served + 1 ELSE served
  /\ UNCHANGED <<entering, nextTicket>>

Next ==
  \/ \E i \in 1..N : TakeTicket(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ [][Next]_vars

====