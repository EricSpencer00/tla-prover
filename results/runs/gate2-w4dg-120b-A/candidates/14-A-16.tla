---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES pc, inCS, ticket, nextTicket

vars == <<pc, inCS, ticket, nextTicket>>

Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

BRequest(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ UNCHANGED inCS

BEnter(i) ==
  /\ pc[i] = "waiting"
  /\ \A j \in 1..N : (pc[j] = "idle") \/ (ticket[j] > ticket[i])
  /\ inCS[i] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, nextTicket>>

BExit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket>>

Next ==
  \/ \E i \in 1..N : BRequest(i)
  \/ \E i \in 1..N : BEnter(i)
  \/ \E i \in 1..N : BExit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : inCS[i] => (\A j \in 1..N : j # i => ~inCS[j])

TypeOK ==
  /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

Inv ==
  /\ MutualExclusion
  /\ TypeOK

StateConstraint ==
  \A i \in 1..N : ticket[i] < MaxNat

====