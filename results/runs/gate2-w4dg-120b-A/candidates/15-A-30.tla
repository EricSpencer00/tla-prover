---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, msgs, sent
vars == <<correct, faulty, pc, msgs, sent>>

Locs == {"not", "hasInit", "sentEcho", "accepted"}
MsgTypes == {"ECHO"}
Msg == [from : 0 .. (N - 1), typ : MsgTypes]

TypeOK ==
  /\ correct \subseteq (0 .. (N - 1))
  /\ faulty \subseteq (0 .. (N - 1))
  /\ pc \in [0 .. (N - 1) -> Locs]
  /\ msgs \in [0 .. (N - 1) -> SUBSET Msg]
  /\ sent \subseteq Msg

AllCorrect == Cardinality(correct) = (N - F)

Init ==
  /\ correct = CHOOSE c \in SUBSET (0 .. (N - 1)) : Cardinality(c) = (N - F)
  /\ faulty = (0 .. (N - 1)) \ correct
  /\ pc = [i \in 0 .. (N - 1) |-> IF i \in correct THEN "hasInit" ELSE "not"]
  /\ msgs = [i \in 0 .. (N - 1) |-> {}]
  /\ sent = {}

InitNoBroadcast ==
  /\ correct = CHOOSE c \in SUBSET (0 .. (N - 1)) : Cardinality(c) = (N - F)
  /\ faulty = (0 .. (N - 1)) \ correct
  /\ pc = [i \in 0 .. (N - 1) |-> "not"]
  /\ msgs = [i \in 0 .. (N - 1) |-> {}]
  /\ sent = {}

Recv(i) ==
  /\ i \in correct
  /\ pc[i] # "accepted"
  /\ msgs' = [msgs EXCEPT ![i] = @ \cup {m \in (sent \cup [from |-> CHOOSE f \in faulty : TRUE, typ |-> "ECHO"]) : TRUE}]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(i) ==
  /\ i \in correct
  /\ pc[i] = "hasInit"
  /\ pc' = [pc EXCEPT ![i] = "sentEcho"]
  /\ sent' = sent \cup {[from |-> i, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, msgs>>

RecvEcho(i) ==
  /\ i \in correct
  /\ pc[i] = "not"
  /\ Cardinality({m \in msgs[i] : m.typ = "ECHO"}) >= (N - 2 * T)
  /\ Cardinality({m \in msgs[i] : m.typ = "ECHO"}) < (N - T)
  /\ pc' = [pc EXCEPT ![i] = "sentEcho"]
  /\ sent' = sent \cup {[from |-> i, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, msgs>>

RecvEchoAccept(i) ==
  /\ i \in correct
  /\ pc[i] \in {"not", "sentEcho"}
  /\ Cardinality({m \in msgs[i] : m.typ = "ECHO"}) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sent' = sent \cup {[from |-> i, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, msgs>>

Accept(i) ==
  /\ i \in correct
  /\ pc[i] = "sentEcho"
  /\ Cardinality({m \in msgs[i] : m.typ = "ECHO"}) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, msgs, sent>>

Next ==
  \/ \E i \in 0 .. (N - 1) : Recv(i)
  \/ \E i \in 0 .. (N - 1) : SendEcho(i)
  \/ \E i \in 0 .. (N - 1) : RecvEcho(i)
  \/ \E i \in 0 .. (N - 1) : RecvEchoAccept(i)
  \/ \E i \in 0 .. (N - 1) : Accept(i)

Fairness == TRUE
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A i \in 0 .. (N - 1) : Fairness => WF_vars(Recv(i)))
  /\ (\A i \in 0 .. (N - 1) : Fairness => SF_vars(SendEcho(i)))
  /\ (\A i \in 0 .. (N - 1) : Fairness => SF_vars(RecvEcho(i)))
  /\ (\A i \in 0 .. (N - 1) : Fairness => SF_vars(RecvEchoAccept(i)))
  /\ (\A i \in 0 .. (N - 1) : Fairness => SF_vars(Accept(i)))

FCConstraints == InitNoBroadcast

UnforgLtl == (\A i \in correct : pc[i] = "not") ~> (\A i \in correct : pc[i] = "not")
CorrLtl == (\A i \in correct : pc[i] = "hasInit") ~> (\A i \in correct : pc[i] = "accepted")
RelayLtl == (\E i \in correct : pc[i] = "accepted") ~> (\A i \in correct : pc[i] = "accepted")
====