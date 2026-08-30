---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, requesting, maxVal, orig
vars == <<inCS, ticket, requesting, maxVal, orig>>

TypeOK ==
  /\ inCS \subseteq 0..(N - 1)
  /\ ticket \in [0..(N - 1) -> 0..MaxNat]
  /\ requesting \subseteq 0..(N - 1)
  /\ maxVal \in 0..MaxNat
  /\ orig \in [0..(N - 1) -> 0..MaxNat]

MutualExclusion ==
  \A a, b \in inCS : a = b

Inv ==
  /\ MutualExclusion
  /\ maxVal <= MaxNat
  /\ \A i \in 0..(N - 1) : ticket[i] <= maxVal

Init ==
  /\ inCS = {}
  /\ ticket = [i \in 0..(N - 1) |-> 0]
  /\ requesting = {}
  /\ maxVal = 0
  /\ orig = [i \in 0..(N - 1) |-> 0]

Requesting(p) ==
  /\ p \notin requesting
  /\ requesting' = requesting \cup {p}
  /\ UNCHANGED <<inCS, ticket, maxVal, orig>>

TakeTicket(p) ==
  /\ p \in requesting
  /\ p \notin inCS
  /\ ticket[p] = 0
  /\ maxVal < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = maxVal + 1]
  /\ maxVal' = maxVal + 1
  /\ orig' = [orig EXCEPT ![p] = maxVal + 1]
  /\ UNCHANGED <<inCS, requesting>>

Enter(p) ==
  /\ p \in requesting
  /\ inCS = {}
  /\ \A q \in 0..(N - 1) : (q \in requesting) => (orig[q] >= ticket[p])
  /\ inCS' = {p}
  /\ UNCHANGED <<ticket, requesting, maxVal, orig>>

Exit(p) ==
  /\ p \in inCS
  /\ inCS' = {}
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ requesting' = requesting \ {p}
  /\ UNCHANGED <<maxVal, orig>>

Next ==
  \/ \E p \in 0..(N - 1) : Requesting(p)
  \/ \E p \in 0..(N - 1) : TakeTicket(p)
  \/ \E p \in 0..(N - 1) : Enter(p)
  \/ \E p \in 0..(N - 1) : Exit(p)

ISpec == Init /\ [][Next]_vars

NatOverride == Nat
====