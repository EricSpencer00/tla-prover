---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* The finite set of natural numbers, overriding the infinite one of the
\* original Bakery spec, is defined by the model checker using Nat.
Naturals == 0..MaxNat

VARIABLES cs, ticket, choosing, served

vars == << cs, ticket, choosing, served >>

TypeOK ==
  /\ cs \in SUBSET (1..N)
  /\ ticket \in [1..N -> Naturals]
  /\ choosing \in [1..N -> BOOLEAN]
  /\ served \in [1..N -> 0..MaxNat]

MutualExclusion == \A p1 \in cs, p2 \in cs : p1 = p2

\* The full inductive invariant of the original Bakery spec, now with the
\* finite ticket range baked in.
Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A p \in 1..N :
       /\ served[p] <= MaxNat
       /\ (p \in cs => ticket[p] <= MaxNat)

Init ==
  /\ cs = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ choosing = [p \in 1..N |-> FALSE]
  /\ served = [p \in 1..N |-> 0]

SetTicket(p, k) ==
  /\ ticket[p] = 0
  /\ k \in Naturals
  /\ ticket' = [ticket EXCEPT ![p] = k]
  /\ UNCHANGED << cs, choosing, served >>

Begin(p) ==
  /\ ticket[p] > 0
  /\ ~ choosing[p]
  /\ \A q \in 1..N : ticket[q] = 0 \/ ticket[q] > ticket[p]
  /\ cs' = cs \cup {p}
  /\ UNCHANGED << ticket, choosing, served >>

Finish(p) ==
  /\ p \in cs
  /\ cs' = cs \ {p}
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ served' = [served EXCEPT ![p] = IF served[p] < MaxNat THEN served[p] + 1 ELSE MaxNat]
  /\ UNCHANGED choosing

Entering == \E p \in 1..N, k \in Naturals : SetTicket(p, k)

Next == Entering \/ (\E p \in 1..N : Begin(p) \/ Finish(p))

ISpec == Init /\ [][Next]_vars

====