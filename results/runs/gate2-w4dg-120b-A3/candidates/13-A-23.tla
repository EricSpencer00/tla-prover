---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The finite natural numbers are obtained by overriding the Nat operator
\* with a version that returns a set bounded by the configured maximum.
NatOverride == 0..MaxNat

ASSUME N \in NatOverride /\ MaxNat \in NatOverride

VARIABLES cs, ticket, asked, nextTicket

vars == << cs, ticket, asked, nextTicket >>

TypeOK ==
  /\ cs \in [1..N -> {"idle", "wanting", "critical"}]
  /\ ticket \in [1..N -> NatOverride]
  /\ asked \subseteq [proc : 1..N, n : NatOverride]
  /\ nextTicket \in NatOverride

MutualExclusion ==
  \A p, q \in 1..N : (cs[p] = "critical" /\ cs[q] = "critical") => p = q

Ordered == \A p \in 1..N, q \in 1..N : (cs[p] = "critical" /\ cs[q] = "wanting") => ticket[p] <= ticket[q]

Inv == TypeOK /\ MutualExclusion /\ Ordered

Init ==
  /\ cs = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ asked = {}
  /\ nextTicket = 0

Want(p) ==
  /\ cs[p] = "idle"
  /\ cs' = [cs EXCEPT ![p] = "wanting"]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ UNCHANGED asked

Enter(p) ==
  /\ cs[p] = "wanting"
  /\ \A q \in 1..N : ticket[p] <= ticket[q]
  /\ cs' = [cs EXCEPT ![p] = "critical"]
  /\ UNCHANGED << ticket, asked, nextTicket >>

Exit(p) ==
  /\ cs[p] = "critical"
  /\ cs' = [cs EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED << asked, nextTicket >>

Next ==
  \/ \E p \in 1..N : Want(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

ISpec == Init /\ [][Next]_vars

Spec == ISpec

====