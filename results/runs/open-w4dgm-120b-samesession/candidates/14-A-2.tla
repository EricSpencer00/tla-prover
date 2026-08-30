---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES holder, status, inCS, tkt, nextTkt, entered

vars == <<holder, status, inCS, tkt, nextTkt, entered>>

\* The behavioural Boulanger spec has no phase counter; the override below is
\* what keeps ticket numbers inside the finite range the model checker can visit.
TypeOK ==
  /\ holder \in 0..N
  /\ status \in {"idle", "contended", "critical"}
  /\ inCS \in 0..N
  /\ tkt \in [1..N -> 0..MaxNat]
  /\ nextTkt \in 0..MaxNat
  /\ entered \in 0..N

Init ==
  /\ holder = 0
  /\ status = "idle"
  /\ inCS = 0
  /\ tkt = [p \in 1..N |-> 0]
  /\ nextTkt = 1
  /\ entered = 0

Request(p) ==
  /\ status = "idle"
  /\ status' = "contended"
  /\ inCS' = p
  /\ tkt' = [tkt EXCEPT ![p] = nextTkt]
  /\ nextTkt' = IF nextTkt < MaxNat THEN nextTkt + 1 ELSE nextTkt
  /\ UNCHANGED <<holder, entered>>

Enter(p) ==
  /\ status = "contended"
  /\ inCS = p
  /\ holder = 0
  /\ holder' = p
  /\ status' = "critical"
  /\ entered' = (entered + 1) % (N + 1)
  /\ UNCHANGED <<inCS, tkt, nextTkt>>

Exit(p) ==
  /\ status = "critical"
  /\ inCS = p
  /\ holder = p
  /\ holder' = 0
  /\ status' = "idle"
  /\ UNCHANGED <<inCS, tkt, nextTkt, entered>>

Next ==
  \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

\* Safety: a process is in the critical section only when it is the one holder.
MutualExclusion == (status = "critical") => (holder = inCS)

\* Liveness under fairness: the critical section is always eventually vacated.
EventualVacate == (status = "critical") ~> (status = "idle")

====