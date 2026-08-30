---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, msgs, sentMsgs
vars == <<correct, faulty, pc, msgs, sentMsgs>>

\* pc values: init-no, init-yes (received the INIT broadcast), echoSent, accepted
PCDomain == {"init-no", "init-yes", "echoSent", "accepted"}
MessageSpace == [sender : 1..N, kind : {"echo"}]

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ correct \cup faulty = (1..N)
  /\ correct \cap faulty = {}
  /\ pc \in [1..N -> PCDomain]
  /\ msgs \in [1..N -> SUBSET MessageSpace]
  /\ sentMsgs \subseteq MessageSpace

Init ==
  /\ correct = {1..(N-F)}
  /\ faulty = {(N-F+1)..N}
  /\ pc = [i \in 1..N |-> IF i <= (N-F) THEN "init-yes" ELSE "init-no"]
  /\ msgs = [i \in 1..N |-> {}]
  /\ sentMsgs = {}

\* No-broadcast variant: every correct process starts without receiving the INIT.
InitNoBroadcast ==
  /\ correct = {1..(N-F)}
  /\ faulty = {(N-F+1)..N}
  /\ pc = [i \in 1..N |-> IF i <= (N-F) THEN "init-no" ELSE "init-no"]
  /\ msgs = [i \in 1..N |-> {}]
  /\ sentMsgs = {}

EchoMsgs(i) == { m \in msgs[i] : m.kind = "echo" }

\* A correct process receives whatever subset of correct-sent and Byzantine-generated ECHOs.
Receive(i) ==
  \E newMsgs \in SUBSET
     ( { [sender |-> j, kind |-> "echo"] : j \in correct } \cup
       { [sender |-> j, kind |-> "echo"] : j \in faulty } ) :
    msgs' = [msgs EXCEPT ![i] = @ \cup newMsgs]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

\* A correct process that received the INIT accepts immediately and ECHOs.
AcceptInit(i) ==
  /\ pc[i] = "init-yes"
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> i, kind |-> "echo"]}
  /\ UNCHANGED <<correct, faulty, msgs>>

\* A correct process sends ECHO once it has enough distinct ECHOs but not yet enough to accept.
EchoOnly(i) ==
  /\ pc[i] # "accepted"
  /\ i \in correct
  /\ Cardinality(EchoMsgs(i)) >= (N - (2 * T))
  /\ Cardinality(EchoMsgs(i)) < (N - T)
  /\ pc' = [pc EXCEPT ![i] = "echoSent"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> i, kind |-> "echo"]}
  /\ UNCHANGED <<correct, faulty, msgs>>

\* A correct process with exactly enough ECHOs both sends and accepts.
EchoAndAccept(i) ==
  /\ pc[i] \notin {"accepted", "echoSent"}
  /\ i \in correct
  /\ Cardinality(EchoMsgs(i)) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> i, kind |-> "echo"]}
  /\ UNCHANGED <<correct, faulty, msgs>>

AcceptPending(i) ==
  /\ pc[i] = "echoSent"
  /\ i \in correct
  /\ Cardinality(EchoMsgs(i)) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, msgs, sentMsgs>>

\* A correct process that already sent ECHO accepts once the threshold is reached.
AcceptEcho(i) ==
  /\ pc[i] = "echoSent"
  /\ i \in correct
  /\ Cardinality(EchoMsgs(i)) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, msgs, sentMsgs>>

AllCorrectAccepted == \A i \in correct : pc[i] = "accepted"

CorrLtl == ( \A i \in correct : pc[i] = "init-yes" ) ~> AllCorrectAccepted
RelayLtl == (\E i \in correct : pc[i] = "accepted") ~> AllCorrectAccepted

\* No-broadcast case: no correct process ever accepts, so message counts stay zero.
UnforgLtl == ( \A i \in correct : pc[i] = "init-no" ) ~> (\A i \in correct : pc[i] # "accepted")

Next ==
  \/ \E i \in 1..N : Receive(i) \/ AcceptInit(i) \/ EchoOnly(i)
                     \/ EchoAndAccept(i) \/ AcceptPending(i) \/ AcceptEcho(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E i \in 1..N : Receive(i))
                              /\ WF_vars(\E i \in 1..N : AcceptInit(i))
                              /\ WF_vars(\E i \in 1..N : EchoAndAccept(i))
                              /\ WF_vars(\E i \in 1..N : AcceptEcho(i))
                              /\ WF_vars(\E i \in 1..N : EchoOnly(i))
                              /\ WF_vars(\E i \in 1..N : AcceptPending(i))

FCConstraints ==
  /\ correct # {}
  /\ N > (3 * T)
  /\ T >= F
  /\ F >= 0
====