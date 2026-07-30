---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

CORR == 1 .. (N - F)
WORR == (N - F + 1) .. N
VARS == <<correct, faulties, pc, inbox, sent>>
Msg == [from : CORR, tp : {"ECHO"}]

Control == {"startB", "startN", "echoed", "accepted"}

TypeOK ==
  /\ correct \subseteq CORR
  /\ Cardinality(correct) = N - F
  /\ faulties = WORR
  /\ pc \in [CORR -> Control]
  /\ inbox \in [CORR -> SUBSET Msg]
  /\ sent \subseteq Msg

Init ==
  /\ \E S \in [CORR -> BOOLEAN] :
       /\ correct = {i \in CORR : S[i]}
       /\ pc = [i \in CORR |-> IF S[i] THEN "startB" ELSE "startN"]
       /\ inbox = [i \in CORR |-> {}]
  /\ sent = {}

InitNoBroad ==
  /\ correct = {i \in CORR : TRUE}
  /\ pc = [i \in CORR |-> "startN"]
  /\ inbox = [i \in CORR |-> {}]
  /\ sent = {}

Recv(i, m) ==
  /\ m \in sent
  /\ m \notin inbox[i]
  /\ inbox' = [inbox EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<correct, faulties, pc, sent>>

RecvStep ==
  /\ \E i \in correct, m \in Msg : Recv(i, m)
  /\ UNCHANGED <<correct, faulties, sent>>

SendEcho(i) ==
  /\ sent' = sent \cup {[from |-> i, tp |-> "ECHO"]}
  /\ pc' = [pc EXCEPT ![i] = "echoed"]
  /\ UNCHANGED <<correct, faulties, inbox>>

SendEchoStep ==
  /\ \E i \in correct : SendEcho(i)
  /\ UNCHANGED <<correct, faulties, inbox>>

Accept(i) ==
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulties, inbox, sent>>

AcceptStep ==
  /\ \E i \in correct : Accept(i)
  /\ UNCHANGED <<correct, faulties, inbox, sent>>

ActEchoAny ==
  /\ \E i \in correct :
       /\ Cardinality({m \in inbox[i] : m.tp = "ECHO"}) >= N - 2 * T
       /\ Cardinality({m \in inbox[i] : m.tp = "ECHO"}) < N - T
       /\ SendEcho(i)
  /\ UNCHANGED <<correct, faulties, inbox, sent>>

ActEchoEnough ==
  /\ \E i \in correct :
       /\ Cardinality({m \in inbox[i] : m.tp = "ECHO"}) >= N - T
       /\ SendEcho(i)
       /\ Accept(i)
  /\ UNCHANGED <<correct, faulties, inbox, sent>>

ActAccept ==
  /\ \E i \in correct :
       /\ pc[i] = "echoed"
       /\ Cardinality({m \in inbox[i] : m.tp = "ECHO"}) >= N - T
       /\ Accept(i)
  /\ UNCHANGED <<correct, faulties, inbox, sent>>

Next ==
  \/ RecvStep
  \/ SendEchoStep
  \/ AcceptStep
  \/ ActEchoAny
  \/ ActEchoEnough
  \/ ActAccept

Spec ==
  /\ Init \/ InitNoBroad
  /\ [][Next]_VARS
  /\ WF_VARS(RecvStep)
  /\ WF_VARS(SendEchoStep)
  /\ WF_VARS(AcceptStep)

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

CorrLtl == <>(\A i \in correct : pc[i] = "accepted")
RelayLtl == (<> (\E i \in correct : pc[i] = "accepted")) ~> (\A i \in correct : pc[i] = "accepted")
UnforgLtl == ((\A i \in correct : pc[i] # "startB") ~> (\A i \in correct : pc[i] = "accepted"))

====