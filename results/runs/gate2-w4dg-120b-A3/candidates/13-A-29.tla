---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES c, ticket, entering
vars == <<c, ticket, entering>>

TypeOK ==
  /\ c \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ entering \subseteq (1..N)

Init ==
  /\ c = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ entering = {}

Request(i) ==
  /\ c[i] = "idle"
  /\ c' = [c EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED entering

Assign(i) ==
  /\ c[i] = "waiting"
  /\ \A j \in 1..N : ticket[j] <= MaxNat
  /\ LET t == IF \E j \in 1..N : c[j] = "idle" /\ ticket[j] = 0
                THEN 1
                ELSE 0
     IN /\ ticket' = [ticket EXCEPT ![i] = t]
        /\ UNCHANGED <<c, entering>>

Enter(i) ==
  /\ c[i] = "waiting"
  /\ \A j \in 1..N : ticket[j] = 0 \/ ticket[j] > ticket[i]
  /\ c' = [c EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<ticket, entering>>

Exit(i) ==
  /\ c[i] = "critical"
  /\ c' = [c EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED entering

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Assign(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

MutualExclusion == \A i \in 1..N : (c[i] = "critical") => (entering = {})
Inv == TypeOK
Spec == Init /\ [][Next]_vars

ISpec == Spec /\ WF_vars(Enter(1) \/ Exit(1))

====