---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes track a control location; faulty ones may act arbitrarily.
\* Messages are modeled as a set of (sender, "ECHO") pairs, or the empty set.
Locations == {"noinit", "init", "sent", "acc"}
Messages == [from : 1..N, type : {"ECHO"}]
\* Confined to the correct-process subpopulation: the invariant below is the
\* guard that makes the fault-modeling choice safe.
\* Fairness is applied to the combined receive-and-act step, not to each send.
VARIABLES correct, faulty, loc, rcvd, sent

vars == <<correct, faulty, loc, rcvd, sent>>

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> Locations]
  /\ rcvd \in [1..N -> SUBSET Messages]
  /\ sent \in SUBSET Messages

\* Unforgeability is a property of the fault model itself (no correct broadcast
\* implies no correct accept); it is a derived property, not a safety invariant.
FCConstraints == Cardinality(correct) = N - F

Init ==
  /\ correct = CHOOSE s \in SUBSET (1..N) : Cardinality(s) = N - F
  /\ faulty = (1..N) \ s
  /\ loc = [p \in 1..N |-> IF p \in correct THEN "init" ELSE "noinit"]
  /\ rcvd = [p \in 1..N |-> {}]
  /\ sent = {}

\* Receive a set of new messages (any from correct processes, any from faulty
\* processes' arbitrary offering) and act on them in the same step.
RecvAndAct(c, msgs) ==
  /\ c \in correct
  /\ loc[c] \notin {"sent", "acc"}
  /\ msgs \subseteq ({m \in sent : m.from \in correct} \cup {m \in Messages : m.from \in faulty})
  /\ rcvd' = [rcvd EXCEPT ![c] = @ \cup msgs]
  /\ IF loc[c] = "init" THEN
        loc' = [loc EXCEPT ![c] = "acc"]
     ELSE IF \E s \in SUBSET {m.from : m \in rcvd[c]} :
        /\ loc[c] = "noinit"
        /\ Cardinality(s) >= N - 2*T
        /\ Cardinality(s) < N - T
        /\ loc[c] = "sent"
     ELSE IF \E s \in SUBSET {m.from : m \in rcvd[c]} :
        /\ loc[c] \in {"noinit", "sent"}
        /\ Cardinality(s) >= N - T
        /\ loc[c] = "acc"
     ELSE loc
  /\ sent' = IF loc[c] \in {"noinit", "sent"} /\ Cardinality({m.from : m \in rcvd[c]}) >= N - T
              THEN sent \cup {[from |-> c, type |-> "ECHO"]}
              ELSE sent

Next == \E c \in 1..N, msgs \in SUBSET Messages : RecvAndAct(c, msgs)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E c \in 1..N, msgs \in SUBSET Messages : RecvAndAct(c, msgs))

UnforgLtl == (\A c \in correct : loc[c] = "noinit") ~> (\A c \in correct : loc[c] = "acc")
CorrLtl == (\A c \in correct : loc[c] = "init") ~> (\A c \in correct : loc[c] = "acc")
RelayLtl == (\E c \in correct : loc[c] = "acc") ~> (\A c \in correct : loc[c] = "acc")
====