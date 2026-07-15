---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

(* Derived sets *)
Proc == 1..N
CorrectProc == { p \in Proc : p \in Correct }
FaultyProc  == Proc \ Correct

(* Message types *)
MsgType == {"ECHO"}

(* A message is a tuple (sender, type) *)
Message == [sender : Proc, type : MsgType]

(* State variables *)
VARIABLES correct,          \* the set of correct processes
          faulty,           \* the set of faulty processes
          pc,               \* control location per process
          received,         \* messages received per process
          sent_msg           \* set of all ECHO messages sent by correct processes

(* Control locations *)
PCVals == {"InitBroadcast", "InitNoBroadcast", "SentEcho", "Accepted"}

(* Type invariant (used as TypeOK) *)
TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty = Proc \ correct
  /\ pc \in [Proc -> PCVals]
  /\ received \in [Proc -> SUBSET Message]
  /\ sent_msg \subseteq {[sender |-> p, type |-> "ECHO"] : p \in correct}

(* Cardinality constraints (FCConstraints) *)
FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ N > 0

(* Initial state: no messages sent/received, partition chosen nondeterministically,
   processes either start having received INIT or not. *)
Init ==
  /\ \E correctInit \subseteq Proc :
        /\ Cardinality(correctInit) = N - F
        /\ correct = correctInit
        /\ faulty = Proc \ correct
        /\ pc = [p \in Proc |-> IF p \in correctInit THEN "InitBroadcast"
                                         ELSE "InitNoBroadcast"]
        /\ received = [p \in Proc |-> {}]
        /\ sent_msg = {}

(* Helper: the set of ECHO messages sent by correct processes *)
EchoSent == sent_msg

(* A correct process may receive any subset of messages that have been sent
   (including arbitrary messages from Byzantine processes) *)
Receive(p) ==
  /\ pc[p] \notin {"Accepted"}  \* once accepted, stay accepted
  /\ LET new == { m \in EchoSent \cup
                      {[sender |-> f, type |-> "ECHO"] : f \in faulty} :
                     m \notin received[p] }
                \* a nondeterministic subset of new messages
        IN received' = [received EXCEPT ![p] = @ \cup Subset(new)]

(* Send an ECHO message *)
SendEcho(p) ==
  /\ pc[p] \in {"InitBroadcast", "InitNoBroadcast", "SentEcho"}
  /\ sent_msg' = sent_msg \cup {[sender |-> p, type |-> "ECHO"}]
  /\ pc' = [pc EXCEPT ![p] = "SentEcho"]

(* Accept *)
Accept(p) ==
  /\ pc[p] \in {"InitBroadcast", "InitNoBroadcast", "SentEcho"}
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED << received, sent_msg >>

(* Count distinct senders of ECHO messages received by p *)
EchoSenders(p) ==
  { m.sender : m \in received[p] }

(* Action for a correct process p *)
CorrectStep(p) ==
  \/ Receive(p)
  \/ /\ pc[p] = "InitBroadcast"
        /\ SendEcho(p)
        /\ Accept(p)
  \/ /\ pc[p] \in {"InitNoBroadcast", "SentEcho"}
        /\ Cardinality(EchoSenders(p)) >= N - 2 * T
        /\ Cardinality(EchoSenders(p)) < N - T
        /\ SendEcho(p)
  \/ /\ pc[p] \in {"InitNoBroadcast", "SentEcho"}
        /\ Cardinality(EchoSenders(p)) >= N - T
        /\ SendEcho(p)
        /\ Accept(p)
  \/ /\ pc[p] = "SentEcho"
        /\ Cardinality(EchoSenders(p)) >= N - T
        /\ Accept(p)

(* Next state relation *)
Next ==
  \E p \in correct : CorrectStep(p)

(* Weak fairness: each correct process eventually executes its step when enabled *)
Fairness ==
  /\ WF_correct(CorrectStep)

(* Full specification *)
Spec == Init /\ [][Next]_<<correct, faulty, pc, received, sent_msg>> /\ Fairness

(* Safety property: Unforgeability *)
UnforgLtl == 
  \A p \in correct : []<>(pc[p] # "Accepted") => []<>(pc[p] = "InitBroadcast")

(* Liveness properties *)
CorrLtl ==
  ( \A p \in correct : pc[p] = "InitBroadcast" ) => <> ( \A p \in correct : pc[p] = "Accepted" )

RelayLtl ==
  ( \E p \in correct : pc[p] = "Accepted" ) => <> ( \A p \in correct : pc[p] = "Accepted" )

=============================================================================