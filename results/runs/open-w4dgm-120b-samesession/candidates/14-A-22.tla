---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

\* Overrides Naturals' Nat with a finite range for model checking.
NatOverride == {0, 1, 2, 3}

CONSTANTS N, MaxNat

VARIABLES phase, ticket, inCS, maxTicket, nextTicket

vars == <<phase, ticket, inCS, maxTicket, nextTicket>>

TypeOK ==
  /\ phase \in {"idle", "reading", "cs"}
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ maxTicket \in 0..MaxNat
  /\ nextTicket \in {1..N}

Init ==
  /\ phase = "idle"
  /\ ticket = [p \in 1..N |-> 0]
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ maxTicket = 0
  /\ nextTicket = 1

Acquire ==
  /\ phase = "idle"
  /\ maxTicket < MaxNat
  /\ nextTicket \in 1..N
  /\ inCS[nextTicket] = FALSE
  /\ phase' = "reading"
  /\ ticket' = [ticket EXCEPT ![nextTicket] = maxTicket + 1]
  /\ maxTicket' = maxTicket + 1
  /\ UNCHANGED <<inCS, nextTicket>>

Enter(p) ==
  /\ phase = "reading"
  /\ ticket[p] = maxTicket
  /\ ~inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ phase' = "cs"
  /\ UNCHANGED <<ticket, maxTicket, nextTicket>>

Leave(p) ==
  /\ phase = "cs"
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ phase' = "idle"
  /\ UNCHANGED <<ticket, maxTicket, nextTicket>>

NextTicket ==
  /\ nextTicket' = IF nextTicket = N THEN 1 ELSE nextTicket + 1
  /\ UNCHANGED <<phase, ticket, inCS, maxTicket>>

Next ==
  \/ Acquire
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Leave(p)
  \/ NextTicket

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => (p = q)

Inv ==
  \A p \in 1..N : inCS[p] => (phase = "cs" /\ ticket[p] = maxTicket)

====