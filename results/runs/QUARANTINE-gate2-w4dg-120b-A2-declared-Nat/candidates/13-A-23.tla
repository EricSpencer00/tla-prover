---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES tc, using, ticket

vars == << tc, using, ticket >>

Last == MaxNat

Lapsed(t) == IF t = Last THEN 0 ELSE t + 1

TypeOK ==
  /\ tc \in [1..N -> {"idle", "sitting", "eating"}]
  /\ using \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]

MutualExclusion ==
  \A i \in 1..N : tc[i] = "eating" => ~using[i]

Inv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ \A i \in 1..N : using[i] => (tc[i] = "eating" \/ tc[i] = "sitting")
  /\ \A i \in 1..N : tc[i] = "sitting" => \E j \in 1..N : (tc[j] = "sitting" /\ j # i /\ ticket[i] > ticket[j])

Init ==
  /\ tc = [i \in 1..N |-> "idle"]
  /\ using = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]

Sit(i) ==
  /\ tc[i] = "idle"
  /\ ~\E j \in 1..N : tc[j] = "sitting" /\ ticket[j] < Lapsed(ticket[i])
  /\ tc' = [tc EXCEPT ![i] = "sitting"]
  /\ ticket' = [ticket EXCEPT ![i] = Lapsed(ticket[i])]
  /\ UNCHANGED using

Eat(i) ==
  /\ tc[i] = "sitting"
  /\ \A j \in 1..N : (tc[j] = "sitting" /\ i # j) => ticket[i] < ticket[j]
  /\ tc' = [tc EXCEPT ![i] = "eating"]
  /\ using' = [using EXCEPT ![i] = TRUE]
  /\ UNCHANGED ticket

Leave(i) ==
  /\ tc[i] = "eating"
  /\ tc' = [tc EXCEPT ![i] = "idle"]
  /\ using' = [using EXCEPT ![i] = FALSE]
  /\ UNCHANGED ticket

Next ==
  \/ \E i \in 1..N : Sit(i)
  \/ \E i \in 1..N : Eat(i)
  \/ \E i \in 1..N : Leave(i)

ISpec == Init /\ [][Next]_vars

NatOverride == Nat

====