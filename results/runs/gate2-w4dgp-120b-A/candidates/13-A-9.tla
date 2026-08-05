---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, tk

vars == <<inCS, want, tk>>

RECURSIVE Max_(S)
Max_(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : \A z \in S : y >= z IN x

MaxTk == Max_(tk)

TypeOK ==
  /\ inCS \in SUBSET (1..N)
  /\ want \in SUBSET (1..N)
  /\ tk \in [1..N -> 0..MaxNat]

Init ==
  /\ inCS = {}
  /\ want = {}
  /\ tk = [i \in 1..N |-> 0]

Request(i) ==
  /\ i \notin want
  /\ want' = want \cup {i}
  /\ UNCHANGED <<inCS, tk>>

Enter(i) ==
  /\ i \in want
  /\ i \notin inCS
  /\ \A j \in inCS : tk[i] < tk[j]
  /\ \A j \in want : tk[i] <= tk[j]
  /\ inCS' = inCS \cup {i}
  /\ want' = want \ {i}
  /\ UNCHANGED <<tk>>

Exit(i) ==
  /\ i \in inCS
  /\ inCS' = inCS \ {i}
  /\ UNCHANGED <<want, tk>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)
  \/ UNCHANGED vars

Inv == MutualExclusion /\ TypeOK /\ Inv

ISpec == Init /\ [][Next]_vars

====