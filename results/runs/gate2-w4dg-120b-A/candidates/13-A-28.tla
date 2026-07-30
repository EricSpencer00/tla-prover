---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

ASSUME MaxNat \in Nat /\ Nat = 0 .. MaxNat

VARIABLES ticket, inCS, waiting

vars == <<ticket, inCS, waiting>>

TypeOK ==
  /\ ticket \in [1..N -> Nat]
  /\ inCS \subseteq (1..N)
  /\ waiting \in [1..N -> BOOLEAN]

MutualExclusion ==
  \A i \in inCS : \A j \in inCS : i = j

Inv ==
  /\ TypeOK
  /\ \A i \in 1..N :
       /\ ticket[i] <= MaxNat
       /\ (i \in inCS => waiting[i])
  /\ inCS \subseteq { i \in 1..N : waiting[i] }

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ inCS = {}
  /\ waiting = [i \in 1..N |-> FALSE]

Request(i) ==
  /\ ~waiting[i]
  /\ \A k \in 1..N : ticket[k] <= ticket[i]
  /\ ticket' = [ticket EXCEPT ![i] = (ticket[i] + 1) % (MaxNat + 1)]
  /\ waiting' = [waiting EXCEPT ![i] = TRUE]
  /\ UNCHANGED inCS

Enter(i) ==
  /\ waiting[i]
  /\ \A k \in 1..N : k \in inCS => ticket[i] < ticket[k]
  /\ inCS' = inCS \cup {i}
  /\ UNCHANGED <<ticket, waiting>>

Exit(i) ==
  /\ i \in inCS
  /\ inCS' = inCS \ {i}
  /\ waiting' = [waiting EXCEPT ![i] = FALSE]
  /\ UNCHANGED ticket

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

ISpec == Init /\ [][Next]_vars

====