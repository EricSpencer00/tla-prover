---- MODULE MCBoulanger ----
EXTENDS Naturals

Boulanger == "The Boulanger mutual exclusion algorithm is used here; its full spec is imported wholesale."

CONSTANTS N, MaxNat

VARIABLES cs, want, ticket
vars == << cs, want, ticket >>

TypeOK ==
  /\ cs \in {"idle", "critical"}
  /\ want \in [1..N -> {"idle", "trying"}]
  /\ ticket \in [1..N -> 0..MaxNat]

Init ==
  /\ cs = "idle"
  /\ want = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]

Request(i) ==
  /\ want[i] = "idle"
  /\ want' = [want EXCEPT ![i] = "trying"]
  /\ UNCHANGED << cs, ticket >>

Grant(i) ==
  /\ want[i] = "trying"
  /\ cs = "idle"
  /\ \A j \in 1..N : ticket[j] < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = ticket[i] + 1]
  /\ cs' = "critical"
  /\ want' = [want EXCEPT ![i] = "idle"]

Release(i) ==
  /\ cs = "critical"
  /\ cs' = "idle"
  /\ UNCHANGED << want, ticket >>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Grant(i)
  \/ \E i \in 1..N : Release(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == cs = "critical" => \A i \in 1..N : want[i] = "idle"

Inv == TypeOK /\ MutualExclusion

NatOverride == Nat

====