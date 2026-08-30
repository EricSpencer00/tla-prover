---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

VARIABLES leader, pstate, wants, ticket

None == 0
Bump(x) == IF x < MaxNat - 1 THEN x + 1 ELSE x

TypeOK ==
  /\ leader \in 0..N
  /\ pstate \in [1..N -> {"idle", "holding", "queued", "crashed"}]
  /\ wants \in [1..N -> 0..MaxNat - 1]
  /\ ticket \in [1..N -> 0..MaxNat - 1]

Init ==
  /\ leader = None
  /\ pstate = [p \in 1..N |-> "idle"]
  /\ wants = [p \in 1..N |-> 0]
  /\ ticket = [p \in 1..N |-> 0]

Request(p) ==
  /\ pstate[p] = "idle"
  /\ pstate' = [pstate EXCEPT ![p] = "queued"]
  /\ wants' = [wants EXCEPT ![p] = Bump(@)]
  /\ UNCHANGED <<leader, ticket>>

Grant(p) ==
  /\ leader = None
  /\ pstate[p] = "queued"
  /\ pstate' = [pstate EXCEPT ![p] = "holding"]
  /\ leader' = p
  /\ ticket' = [ticket EXCEPT ![p] = Bump(@)]
  /\ UNCHANGED wants

Release(p) ==
  /\ leader = p
  /\ pstate[p] = "holding"
  /\ pstate' = [pstate EXCEPT ![p] = "idle"]
  /\ leader' = None
  /\ UNCHANGED <<wants, ticket>>

Crash(p) ==
  /\ pstate[p] # "crashed"
  /\ pstate' = [pstate EXCEPT ![p] = "crashed"]
  /\ leader' = IF leader = p THEN None ELSE leader
  /\ UNCHANGED <<wants, ticket>>

Recover(p) ==
  /\ pstate[p] = "crashed"
  /\ pstate' = [pstate EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<leader, wants, ticket>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Grant(p)
  \/ \E p \in 1..N : Release(p)
  \/ \E p \in 1..N : Crash(p)
  \/ \E p \in 1..N : Recover(p)

Spec == Init /\ [][Next]_<<leader, pstate, wants, ticket>>

MutualExclusion == \A p \in 1..N : (pstate[p] = "holding") => (leader = p)

Inv == MutualExclusion /\ TypeOK

TicketBound == \A p \in 1..N : ticket[p] < MaxNat

====