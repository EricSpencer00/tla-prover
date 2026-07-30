---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES ticket, choosing, inCS, served

vars == <<ticket, choosing, inCS, served>>

Range(t) == {t[i] : i \in 1..N}

TypeOK ==
  /\ ticket \in [1..N -> Nat]
  /\ choosing \in [1..N -> BOOLEAN]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ served \in 0..MaxNat

MutualExclusion == \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

Inv == MutualExclusion /\ TypeOK

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ served = 0

Choose(i) ==
  /\ ~choosing[i]
  /\ ~inCS[i]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, inCS, served>>

Assign(i) ==
  /\ choosing[i]
  /\ ticket' = [ticket EXCEPT ![i] = Cardinality({j \in 1..N : ticket[j] > ticket[i]}) + 1]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<inCS, served>>

Enter(i) ==
  /\ ~inCS[i]
  /\ ticket[i] # 0
  /\ \A j \in 1..N : ticket[j] = 0 \/ ticket[i] < ticket[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, choosing, served>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ served' = (served + 1) % (MaxNat + 1)
  /\ UNCHANGED choosing

Next ==
  \/ \E i \in 1..N : Choose(i)
  \/ \E i \in 1..N : Assign(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ WF_vars(\E i \in 1..N : Enter(i))

NatOverride == Nat
====