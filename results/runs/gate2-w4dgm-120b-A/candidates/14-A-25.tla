---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES pc, tkt, waiting, inCS

TypeOK ==
  /\ pc \in [1..N -> {"idle", "waiting", "cs"}]
  /\ tkt \in [1..N -> 0..MaxNat]
  /\ waiting \subseteq 1..N
  /\ inCS \subseteq 1..N

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ tkt = [p \in 1..N |-> 0]
  /\ waiting = {}
  /\ inCS = {}

Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ waiting' = waiting \cup {p}
  /\ UNCHANGED <<tkt, inCS>>

Enter(p) ==
  /\ pc[p] = "waiting"
  /\ p \in waiting
  /\ \A q \in waiting : p <= q
  /\ \A q \in inCS : p < q
  /\ \A q \in waiting : q = p \/ q \notin waiting
  /\ tkt[p] < MaxNat
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ inCS' = inCS \cup {p}
  /\ waiting' = waiting \ {p}
  /\ tkt' = [tkt EXCEPT ![p] = @ + 1]

Exit(p) ==
  /\ pc[p] = "cs"
  /\ inCS' = inCS \ {p}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<tkt, waiting>>

Next ==
  \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_<<pc, tkt, waiting, inCS>>

MutualExclusion == \A p \in inCS : pc[p] = "cs"

Inv == TypeOK /\ MutualExclusion

====