---- MODULE MCBoulanger ----
EXTENDS Integers, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES status, ticket

vars == <<status, ticket>>

TypeOK ==
  /\ status \in [1..N -> {"idle", "trying", "critical"}]
  /\ ticket \in [1..N -> Nat]

Init ==
  /\ status = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]

Acquiring(i) ==
  /\ status[i] = "idle"
  /\ status' = [status EXCEPT ![i] = "trying"]
  /\ UNCHANGED ticket

Critical(i) ==
  /\ status[i] = "trying"
  /\ \A j \in 1..N : status[j] = "trying" => ticket[i] <= ticket[j]
  /\ status' = [status EXCEPT ![i] = "critical"]
  /\ UNCHANGED ticket

Leaving(i) ==
  /\ status[i] = "critical"
  /\ status' = [status EXCEPT ![i] = "idle"]
  /\ UNCHANGED ticket

Ticket(i) ==
  /\ status[i] = "trying"
  /\ ticket[i] < MaxNat
  /\ \E k \in 1..N :
       /\ ticket[k] >= ticket[i]
       /\ ticket[k] < MaxNat
       /\ ticket' = [ticket EXCEPT ![i] = ticket[k] + 1]
  /\ UNCHANGED status

Next ==
  \E i \in 1..N :
    \/ Acquiring(i)
    \/ Critical(i)
    \/ Leaving(i)
    \/ Ticket(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (status[i] = "critical" /\ status[j] = "critical") => i = j

Inv ==
  /\ status \in [1..N -> {"idle", "trying", "critical"}]
  /\ ticket \in [1..N -> Nat]

StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====