---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

ASSUME N \in Nat \ {0}

VARIABLES status, ticket

vars == <<status, ticket>>

Range(f) == {f[i] : i \in 1..N}

TypeOK ==
  /\ status \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> Nat]

Init ==
  /\ status = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]

Request(i) ==
  /\ status[i] = "idle"
  /\ status' = [status EXCEPT ![i] = "waiting"]
  /\ UNCHANGED ticket

Enter(i) ==
  /\ status[i] = "waiting"
  /\ \A j \in 1..N : status[j] # "critical"
  /\ ticket' = [ticket EXCEPT ![i] = MaxNat - 1]
  /\ status' = [status EXCEPT ![i] = "critical"]

Exit(i) ==
  /\ status[i] = "critical"
  /\ status' = [status EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N : Request(i))
  /\ WF_vars(\E i \in 1..N : Enter(i))
  /\ WF_vars(\E i \in 1..N : Exit(i))

MutualExclusion ==
  (Cardinality({i \in 1..N : status[i] = "critical"}) <= 1)

Inv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ status \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> 0..(MaxNat - 1)]

====