---- MODULE MCBakery --------------------------------
EXTENDS Bakery

ASSUME MaxNat \in Nat

CONSTANT NatOverride

VARIABLES inCS, entering, clock
vars == <<inCS, entering, clock>>

TypeOK ==
  /\ inCS \subseteq NatOverride
  /\ entering \subseteq NatOverride
  /\ clock \in 0 .. MaxNat

Init ==
  /\ inCS = {}
  /\ entering = {}
  /\ clock = 0

Request(n) ==
  /\ n \notin inCS
  /\ n \notin entering
  /\ entering' = entering \cup {n}
  /\ UNCHANGED <<inCS, clock>>

Enter(n) ==
  /\ n \in entering
  /\ entering' = entering \ {n}
  /\ inCS' = inCS \cup {n}
  /\ UNCHANGED clock

Exit(n) ==
  /\ n \in inCS
  /\ inCS' = inCS \ {n}
  /\ UNCHANGED <<entering, clock>>

Tick ==
  /\ clock' = (clock + 1) % (MaxNat + 1)
  /\ UNCHANGED <<inCS, entering>>

Next ==
  \/ \E n \in NatOverride : Request(n)
  \/ \E n \in NatOverride : Enter(n)
  \/ \E n \in NatOverride : Exit(n)
  \/ Tick

Spec == Init /\ [][Next]_vars

MutualExclusion == \A m, n \in NatOverride : (m \in inCS /\ n \in inCS) => m = n

ClockBound == clock = MaxNat

====