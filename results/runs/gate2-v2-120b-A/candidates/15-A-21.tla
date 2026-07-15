---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F

(* ------------------------------------------------------------------------- *)
(* Derived sets                                                               *)
(* ------------------------------------------------------------------------- *)
Proc  == 1..N
ECHO  == "ECHO"

(* ------------------------------------------------------------------------- *)
(* State variables                                                            *)
(* ------------------------------------------------------------------------- *)
VARIABLES correct, faulty, pc, recv, sent

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                         *)
(* ------------------------------------------------------------------------- *)

InitCorrectSet == { i \in Proc : i <= N - F }
InitFaultySet  == Proc \ InitCorrectSet

PCVals == {"InitNo", "InitYes", "EchoSent", "Accepted"}

Message == [type : {"ECHO"}, sender : Proc]

(* ------------------------------------------------------------------------- *)
(* Initial state                                                              *)
(* ------------------------------------------------------------------------- *)
Init ==
  /\ correct = InitCorrectSet
  /\ faulty  = InitFaultySet
  /\ pc      = [i \in Proc |-> IF i \in correct THEN "InitNo" ELSE "InitNo"]
  /\ recv    = [i \in Proc |-> {}]
  /\ sent    = {}

(* ------------------------------------------------------------------------- *)
(* Actions                                                                    *)
(* ------------------------------------------------------------------------- *)

(* A correct process may receive any subset of messages that have been sent
   by correct processes plus any arbitrary messages from Byzantine processes. *)
Receive(i) ==
  /\ i \in correct
  /\ \E newMsgs \in SUBSET ({ m \in sent : m.sender \in correct } \cup
                           { [type |-> "ECHO", sender |-> b] : b \in faulty }):
        /\ recv' = [recv EXCEPT ![i] = recv[i] \cup newMsgs]
        /\ UNCHANGED <<correct, faulty, pc, sent>>

(* If a correct process started with the INIT message, it immediately sends
   an ECHO and accepts. *)
InitYesAction(i) ==
  /\ i \in correct
  /\ pc[i] = "InitYes"
  /\ pc'   = [pc EXCEPT ![i] = "Accepted"]
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> i] }
  /\ UNCHANGED <<recv, correct, faulty>>

(* Correct process that has not yet sent ECHO receives at least N-2T distinct
   ECHO messages (but fewer than N-T) and then sends ECHO. *)
EchoWhenLow(i) ==
  /\ i \in correct
  /\ pc[i] = "InitNo"
  /\ Let echSet == { m.sender : m \in recv[i] } IN
        /\ Cardinality(echSet) >= N - 2*T
        /\ Cardinality(echSet) < N - T
        /\ pc'   = [pc EXCEPT ![i] = "EchoSent"]
        /\ sent' = sent \cup { [type |-> "ECHO", sender |-> i] }
        /\ UNCHANGED <<recv, correct, faulty>>

(* Correct process that has not yet sent ECHO receives at least N-T distinct
   ECHO messages and then sends ECHO and accepts. *)
EchoAndAcceptHigh(i) ==
  /\ i \in correct
  /\ pc[i] = "InitNo"
  /\ Let echSet == { m.sender : m \in recv[i] } IN
        /\ Cardinality(echSet) >= N - T
        /\ pc'   = [pc EXCEPT ![i] = "Accepted"]
        /\ sent' = sent \cup { [type |-> "ECHO", sender |-> i] }
        /\ UNCHANGED <<recv, correct, faulty>>

(* A correct process that has already sent ECHO receives at least N-T distinct
   ECHO messages and then accepts. *)
AcceptAfterEcho(i) ==
  /\ i \in correct
  /\ pc[i] = "EchoSent"
  /\ Let echSet == { m.sender : m \in recv[i] } IN
        /\ Cardinality(echSet) >= N - T
        /\ pc' = [pc EXCEPT ![i] = "Accepted"]
        /\ UNCHANGED <<recv, sent, correct, faulty>>

(* Byzantine processes may send arbitrary messages at any time. *)
ByzSend ==
  /\ \E b \in faulty, r \in Proc :
        /\ sent' = sent \cup { [type |-> "ECHO", sender |-> b] }
        /\ UNCHANGED <<recv, pc, correct, faulty>>

(* ------------------------------------------------------------------------- *)
(* Next-state relation                                                         *)
(* ------------------------------------------------------------------------- *)
Next ==
  \/ \E i \in Proc : Receive(i)
  \/ \E i \in correct : InitYesAction(i)
  \/ \E i \in correct : EchoWhenLow(i)
  \/ \E i \in correct : EchoAndAcceptHigh(i)
  \/ \E i \in correct : AcceptAfterEcho(i)
  \/ ByzSend

(* ------------------------------------------------------------------------- *)
(* Specification                                                               *)
(* ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<pc, recv, sent, correct, faulty>>

(* ------------------------------------------------------------------------- *)
(* Safety invariant (type correctness)                                         *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty  \subseteq Proc
  /\ correct \cap faulty = {}
  /\ pc \in [Proc -> PCVals]
  /\ sent \subseteq { [type |-> "ECHO", sender |-> p] : p \in Proc }
  /\ \A i \in Proc : recv[i] \subseteq sent

(* ------------------------------------------------------------------------- *)
(* Safety invariant for the problem statement                                  *)
(* ------------------------------------------------------------------------- *)
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* ------------------------------------------------------------------------- *)
(* Liveness properties (using temporal operators)                             *)
(* ------------------------------------------------------------------------- *)
CorrLtl == []<>(\A i \in correct : pc[i] = "Accepted")
RelayLtl == [](\E i \in correct : pc[i] = "Accepted") => <> (\A i \in correct : pc[i] = "Accepted")
UnforgLtl == [](\A i \in correct : pc[i] # "Accepted") \/ (<> (\A i \in correct : pc[i] = "Accepted"))

=============================================================================