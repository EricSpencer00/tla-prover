---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

\* The Boulanger mutual exclusion algorithm, with the infinite Nat type
\* overridden by a finite range for model checking. The full
\* behavioral system is modeled (not the inductive specification), and
\* a state constraint keeps all ticket numbers inside the finite range.
CONSTANTS N, MaxNat

VARIABLES active, want, ticket, maxTicket

TypeOK ==
  /\ active \in 0..N
  /\ want \subseteq 1..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ maxTicket \in 0..MaxNat

Init ==
  /\ active = 0
  /\ want = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ maxTicket = 0

Request(p) ==
  /\ p \notin want
  /\ active # 0
  /\ want' = want \cup {p}
  /\ UNCHANGED <<active, ticket, maxTicket>>

Enter(p) ==
  /\ p \in want
  /\ active = 0
  /\ active' = p
  /\ ticket' = [ticket EXCEPT ![p] = maxTicket]
  /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
  /\ want' = want \ {p}

Release(p) ==
  /\ active = p
  /\ active' = 0
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<want, maxTicket>>

Next ==
  \/ \E p \in 1..N : Request(p) \/ Enter(p) \/ Release(p)

Spec == Init /\ [][Next]_<<active, want, ticket, maxTicket>>

MutualExclusion == active >= 1 => (active \notin want /\ ticket[active] > 0)

Inv ==
  /\ active >= 1 => (active \notin want /\ ticket[active] > 0)
  /\ want \cap {p \in 1..N : ticket[p] > 0} = {}

WithinFiniteNatRange == \A p \in 1..N : ticket[p] < MaxNat

====