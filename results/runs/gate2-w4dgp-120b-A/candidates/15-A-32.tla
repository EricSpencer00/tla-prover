---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

MessageType == {"ECHO"}
NoMsg == [sender |-> N, typ |-> "NOMSG"]

VARIABLES correct, faulty, pc, msgs, sentmsgs

vars == <<correct, faulty, pc, msgs, sentmsgs>>

AllProcs == 0..(N - 1)
SentMsgsSet == { [sender |-> s, typ |-> "ECHO"] : s \in correct }

TypeOK ==
  /\ correct \subseteq AllProcs /\ faulty \subseteq AllProcs /\ correct = AllProcs \ faulty
  /\ pc \in [AllProcs -> {"noinit", "init", "echoed", "accept"}]
  /\ msgs \in [AllProcs -> SUBSET SentMsgsSet \cup {NoMsg}]
  /\ (sentmsgs = {} \/ sentmsgs = SentMsgsSet)

Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = AllProcs \ correct
  /\ Cardinality(correct) > 3 * T
  /\ T >= F
  /\ \E S \in ({0, 1} \ {0}) ^ N :
       /\ \A i \in AllProcs : pc[i] = (IF S[i] = 1 THEN "init" ELSE "noinit")
       /\ \A i \in AllProcs : msgs[i] = {}
  /\ sentmsgs = {}

InitAll ==
  /\ Cardinality(correct) = N - F
  /\ faulty = AllProcs \ correct
  /\ Cardinality(correct) > 3 * T
  /\ T >= F
  /\ \A i \in AllProcs : pc[i] = "noinit"
  /\ \A i \in AllProcs : msgs[i] = {}
  /\ sentmsgs = {}

Receive(i) ==
  /\ pc[i] \in {"init", "echoed", "accept"}
  /\ \E S \subseteq sentmsgs \cup {[sender |-> j, typ |-> "ECHO"] : j \in faulty} :
       msgs' = [msgs EXCEPT ![i] = msgs[i] \cup S]
  /\ UNCHANGED <<correct, faulty, pc, sentmsgs>>

CorEcho(i) ==
  /\ pc[i] = "init"
  /\ ~ \E m \in msgs[i] : m.typ = "ECHO"
  /\ pc' = [pc EXCEPT ![i] = "echoed"]
  /\ sentmsgs' = sentmsgs \cup {[sender |-> i, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, msgs>>

CorEchoThresh(i) ==
  /\ pc[i] = "noinit"
  /\ Cardinality({ m \in msgs[i] : m.typ = "ECHO" }) >= N - 2 * T
  /\ Cardinality({ m \in msgs[i] : m.typ = "ECHO" }) < N - T
  /\ pc' = [pc EXCEPT ![i] = "echoed"]
  /\ sentmsgs' = sentmsgs \cup {[sender |-> i, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, msgs>>

CorEchoCoincide(i) ==
  /\ pc[i] = "noinit"
  /\ Cardinality({ m \in msgs[i] : m.typ = "ECHO" }) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "echoed"]
  /\ sentmsgs' = sentmsgs \cup {[sender |-> i, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, msgs>>

CorAccept(i) ==
  /\ pc[i] = "echoed"
  /\ Cardinality({ m \in msgs[i] : m.typ = "ECHO" }) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ UNCHANGED <<correct, faulty, msgs, sentmsgs>>

Next ==
  \/ \E i \in AllProcs : Receive(i)
  \/ \E i \in correct : CorEcho(i)
  \/ \E i \in correct : CorEchoThresh(i)
  \/ \E i \in correct : CorEchoCoincide(i)
  \/ \E i \in correct : CorAccept(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in AllProcs : Receive(i))
  /\ \A i \in correct : WF_vars(CorEcho(i))
  /\ \A i \in correct : WF_vars(CorEchoThresh(i))
  /\ \A i \in correct : WF_vars(CorEchoCoincide(i))
  /\ \A i \in correct : WF_vars(CorAccept(i))

NoBroadProp == (\A i \in correct : pc[i] = "noinit") ~> (\A i \in correct : pc[i] = "accept")
CorrProp == (\A i \in correct : pc[i] = "init") ~> (\A i \in correct : pc[i] = "accept")
RelayProp == (\E i \in correct : pc[i] = "accept") ~> (\A i \in correct : pc[i] = "accept")

FCConstraints == Cardinality(correct) > 3 * T /\ T >= F

====