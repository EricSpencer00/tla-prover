---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS
  N, MaxNat

VARIABLES
  active, ticket, entering

vars == <<active, ticket, entering>>

TypeOK ==
  /\ active \subseteq (1..N)
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ entering \in [1..N -> BOOLEAN]

MutualExclusion ==
  \A a, b \in active : a = b

Inv ==
  /\ TypeOK
  /\ MutualExclusion

Init ==
  /\ active = {}
  /\ ticket = [i \in 1..N |-> 0]
  /\ entering = [i \in 1..N |-> FALSE]

Enter(i) ==
  /\ i \notin active
  /\ entering[i] = FALSE
  /\ entering' = [entering EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<active, ticket>>

Take(i) ==
  /\ i \notin active
  /\ entering[i] = TRUE
  /\ ticket' = [ticket EXCEPT ![i] = 1 + (IF \E j \in active : ticket[j] # 0 THEN Max(\{ticket[j] : j \in active}) ELSE 0)]
  /\ active' = active \cup {i}
  /\ entering' = [entering EXCEPT ![i] = FALSE]

Exit(i) ==
  /\ i \in active
  /\ active' = active \ {i}
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED entering

Next ==
  \E i \in 1..N : Enter(i) \/ Take(i) \/ Exit(i)

ISpec == Init /\ [][Next]_vars

NatOverride == Nat
====