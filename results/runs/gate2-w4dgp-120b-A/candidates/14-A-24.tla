---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

ASSUME N \in Nat /\ N >= 1 /\ MaxNat \in Nat /\ MaxNat >= 1

VARIABLES pc, ticket, busy

vars == <<pc, ticket, busy>>

Range(x) == {x[i] : i \in DOMAIN x}

InitProc == CHOOSE i \in DOMAIN pc : TRUE

TypeOK ==
  /\ pc \in [{1, 2, 3} -> {"idle", "waiting", "critical"}]
  /\ ticket \in [{1, 2, 3} -> 0..MaxNat]
  /\ busy \in BOOLEAN

Avail == {i \in 1..N : pc[i] # "critical"}

Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ busy = FALSE

Acquiring(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ UNCHANGED <<ticket, busy>>

Requesting(i) ==
  /\ pc[i] = "waiting"
  /\ busy = FALSE
  /\ Avail = {}
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ busy' = TRUE
  /\ pc' = [pc EXCEPT ![i] = "critical"]

Racing(i) ==
  /\ pc[i] = "waiting"
  /\ busy = TRUE
  /\ ticket' = [ticket EXCEPT ![i] = ticket[i] + 1]
  /\ UNCHANGED <<pc, busy>>

Leaving(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, busy>>

Next ==
  \/ \E i \in 1..N : Acquiring(i)
  \/ \E i \in 1..N : Requesting(i)
  \/ \E i \in 1..N : Racing(i)
  \/ \E i \in 1..N : Leaving(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A a, b \in 1..N : (pc[a] = "critical" /\ pc[b] = "critical") => a = b

Inv ==
  /\ busy => \E i \in 1..N : pc[i] = "critical"
  /\ ~busy => \E i \in 1..N : pc[i] = "idle"
  /\ busy => \A i \in 1..N : ticket[i] <= MaxNat

StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====