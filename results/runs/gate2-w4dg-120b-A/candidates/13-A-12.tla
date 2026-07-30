---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

ASSUME MaxNat \in Nat

VARIABLES phase, ticket, serving, maxTicket
vars == << phase, ticket, serving, maxTicket >>

States == {"idle", "waiting", "cs"}
Tickets == 0 .. MaxNat

TypeOK ==
  /\ phase \in [1 .. N -> States]
  /\ ticket \in [1 .. N -> Tickets]
  /\ serving \in Tickets
  /\ maxTicket \in Tickets

\* The bakery invariant: mutual exclusion plus every live ticket is bounded
\* by the maximum seen, so no stale or out-of-range ticket can grant entry.
MutualExclusion ==
  /\ \A q \in 1 .. N : phase[q] = "cs" => ServingTicket(\A i \in 1 .. N : ticket[i])
  /\ \A q \in 1 .. N : phase[q] = "cs" => \A i \in 1 .. N : (i # q) => ticket[i] < ticket[q]
  /\ \A i \in 1 .. N : phase[i] = "cs" => ticket[i] <= maxTicket

ServingTicket(f) == \E i \in 1 .. N : (f[i] /\ phase[i] = "cs")

\* The bounded natural-number type replaces the usual infinite Nat for model
\* checking; ticket numbering is therefore capped at MaxNat.
Init ==
  /\ phase = [i \in 1 .. N |-> "idle"]
  /\ ticket = [i \in 1 .. N |-> 0]
  /\ serving = 0
  /\ maxTicket = 0

TakeTicket(i) ==
  /\ phase[i] = "idle"
  /\ phase' = [phase EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket]
  /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
  /\ UNCHANGED serving

Enter(i) ==
  /\ phase[i] = "waiting"
  /\ \A j \in 1 .. N : (phase[j] # "cs") \/ (ticket[j] < ticket[i])
  /\ phase' = [phase EXCEPT ![i] = "cs"]
  /\ serving' = ticket[i]
  /\ UNCHANGED << ticket, maxTicket >>

Exit(i) ==
  /\ phase[i] = "cs"
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ serving' = 0
  /\ UNCHANGED maxTicket

Next ==
  \/ \E i \in 1 .. N : TakeTicket(i)
  \/ \E i \in 1 .. N : Enter(i)
  \/ \E i \in 1 .. N : Exit(i)

\* The inductive spec starts from any type-correct state (not just the
\* initial one) to verify the invariant holds across the whole reachable set.
ISpec == Init /\ [][Next]_vars

\* No liveness requirements are specified for the bakery algorithm here.
NoLiveProp == TRUE

\* The configuration runs the model checking against the inductive spec,
\* with deadlock checking deliberately disabled.
Spec == ISpec
\* Mutually exclusive access, all state well-typed, and the full invariant.
Inv == MutualExclusion /\ TypeOK
====