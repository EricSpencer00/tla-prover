---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, loc, rx, sentBy

vars == <<correct, faulty, loc, rx, sentBy>>

MsgTypes == {"ECHO"}
Msgs == [from : 1..N, tp : MsgTypes]

InitLocs == {"broadcast", "noBroadcast"}
Stages == {"init", "hasEcho", "accepted"}

RECURSIVE FromsOf(_)
FromsOf(S) == IF S = {} THEN {}
              ELSE LET m == CHOOSE x \in S : TRUE
                   IN {m.from} \cup FromsOf(S \ {m})

Init ==
  /\ correct = {1 .. (N - F)}
  /\ faulty = {1 .. N} \ correct
  /\ loc \in [1..N -> Stages]
  /\ rx \in [1..N -> SUBSET Msgs]
  /\ sentBy = {}

InitAllBroadcast ==
  /\ Init
  /\ \A i \in 1..N : loc[i] = "broadcast"

InitNoBroadcast ==
  /\ Init
  /\ \A i \in 1..N : loc[i] = "noBroadcast"

CorrectReceive(i) ==
  /\ i \in correct
  /\ i \notin faulty
  /\ \E M \in SUBSET (sentBy \cup {[from |-> j, tp |-> "ECHO"] : j \in faulty}) : rx' = [rx EXCEPT ![i] = M]
  /\ UNCHANGED <<correct, faulty, loc, sentBy>>

CorrectBroadcast(i) ==
  /\ i \in correct
  /\ loc[i] = "broadcast"
  /\ loc' = [loc EXCEPT ![i] = "hasEcho"]
  /\ sentBy' = sentBy \cup {[from |-> i, tp |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, rx>>

CorrectEchoPartial(i) ==
  /\ i \in correct
  /\ loc[i] = "init"
  /\ Cardinality(FromsOf(rx[i])) >= (N - 2 * T)
  /\ Cardinality(FromsOf(rx[i])) < (N - T)
  /\ loc' = [loc EXCEPT ![i] = "hasEcho"]
  /\ sentBy' = sentBy \cup {[from |-> i, tp |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, rx>>

CorrectEchoFull(i) ==
  /\ i \in correct
  /\ loc[i] = "init"
  /\ Cardinality(FromsOf(rx[i])) >= (N - T)
  /\ loc' = [loc EXCEPT ![i] = "hasEcho"]
  /\ sentBy' = sentBy \cup {[from |-> i, tp |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, rx>>

CorrectAccept(i) ==
  /\ i \in correct
  /\ loc[i] = "hasEcho"
  /\ Cardinality(FromsOf(rx[i])) >= (N - T)
  /\ loc' = [loc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, rx, sentBy>>

Next ==
  \E i \in 1..N : CorrectReceive(i) \/ CorrectBroadcast(i) \/ CorrectEchoPartial(i) \/ CorrectEchoFull(i) \/ CorrectAccept(i)

Spec == Init /\ [][Next]_vars
        /\ \A i \in 1..N : WF_vars(CorrectReceive(i))
        /\ \A i \in 1..N : WF_vars(CorrectEchoFull(i))
        /\ \A i \in 1..N : SF_vars(CorrectAccept(i))

TypeOK ==
  /\ correct \subseteq (1..N) /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> Stages]
  /\ rx \in [1..N -> SUBSET Msgs]
  /\ sentBy \subseteq Msgs

FCConstraints ==
  /\ correct \cap faulty = {}
  /\ \A i \in correct : loc[i] \in Stages
  /\ \A i \in faulty : loc[i] \notin Stages

CorrLtl == \A i \in correct : (loc[i] = "broadcast") ~> (loc[i] = "accepted")

RelayLtl == (\E i \in correct : loc[i] = "accepted") ~> (\A i \in correct : loc[i] = "accepted")

UnforgLtl == (\A i \in correct : loc[i] = "noBroadcast") ~> (\A i \in correct : loc[i] # "accepted")

====