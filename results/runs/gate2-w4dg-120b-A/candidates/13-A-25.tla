---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES entering, ticket, nextTicket, active

vars == <<entering, ticket, nextTicket, active>>

TypeOK ==
  /\ entering \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ active \in SUBSET (1..N)

MutualExclusion ==
  \A i, j \in active : i = j

Inv ==
  /\ entering \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ active \subseteq (1..N)

Init ==
  /\ entering = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ active = {}

Enter(i) ==
  /\ ~entering[i]
  /\ i \notin active
  /\ nextTicket < MaxNat
  /\ entering' = [entering EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED active

Critical(i) ==
  /\ entering[i]
  /\ entering' = [entering EXCEPT ![i] = FALSE]
  /\ active' = active \cup {i}
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(i) ==
  /\ i \in active
  /\ active' = active \ {i}
  /\ UNCHANGED <<entering, ticket, nextTicket>>

Next ==
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Critical(i)
  \/ \E i \in 1..N : Exit(i)

ISpec == Init /\ [][Next]_vars

====