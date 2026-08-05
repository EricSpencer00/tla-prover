---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket, turn
vars == <<inCS, want, ticket, nextTicket, turn>>

NatOverride == 0 .. MaxNat

TypeOK ==
  /\ inCS \in BOOLEAN
  /\ want \in {{1 .. N}}
  /\ ticket \in [1 .. N -> NatOverride]
  /\ nextTicket \in NatOverride
  /\ turn \in [1 .. N -> NatOverride]

Init ==
  /\ inCS = FALSE
  /\ want = {}
  /\ ticket = [i \in 1 .. N |-> 0]
  /\ nextTicket = 0
  /\ turn = [i \in 1 .. N |-> 0]

Arrive(i) ==
  /\ i \notin want
  /\ want' = want \cup {i}
  /\ UNCHANGED <<inCS, ticket, nextTicket, turn>>

GetTicket(i) ==
  /\ i \in want
  /\ ticket[i] = 0
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ UNCHANGED <<inCS, want, turn>>

Enter(i) ==
  /\ i \in want
  /\ ~inCS
  /\ ticket[i] # 0
  /\ turn' = [turn EXCEPT ![i] = ticket[i]]
  /\ inCS' = TRUE
  /\ UNCHANGED <<want, ticket, nextTicket>>

Exit ==
  /\ inCS
  /\ inCS' = FALSE
  /\ want' = {}
  /\ ticket' = [i \in 1 .. N |-> 0]
  /\ UNCHANGED <<nextTicket, turn>>

Next ==
  \/ \E i \in 1 .. N : Arrive(i)
  \/ \E i \in 1 .. N : GetTicket(i)
  \/ \E i \in 1 .. N : Enter(i)
  \/ Exit

ISpec == Init /\ [][Next]_vars

MutualExclusion == inCS => (want # {})
TypeOKInv == TypeOK
Inv == MutualExclusion /\ TypeOKInv

====