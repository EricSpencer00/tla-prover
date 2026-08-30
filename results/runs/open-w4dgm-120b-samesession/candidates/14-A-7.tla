---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES cs, want, ticket, nextTicket

vars == <<cs, want, ticket, nextTicket>>

Init ==
  /\ cs = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

Request(p) ==
  /\ ~want[p]
  /\ ~cs[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED cs

Enter(p) ==
  /\ want[p]
  /\ ~cs[p]
  /\ ticket[p] = 0
  /\ \A q \in 1..N : ~cs[q]
  /\ cs' = [cs EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<want, ticket, nextTicket>>

Pass(p) ==
  /\ cs[p]
  /\ cs' = [cs EXCEPT ![p] = FALSE]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket>>

Reissue(p) ==
  /\ ~cs[p]
  /\ want[p]
  /\ ticket[p] > 0
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<cs, want, nextTicket>>

Next ==
  \E p \in 1..N :
    Request(p) \/ Enter(p) \/ Pass(p) \/ Reissue(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 1..N : cs[p] => (\A q \in 1..N \ {p} : ~cs[q])

TypeOK ==
  /\ cs \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A p, q \in 1..N :
       (cs[p] /\ cs[q]) => p = q
  /\ \A p \in 1..N : cs[p] => ticket[p] = 0

BoundedNat == nextTicket <= MaxNat

====