---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

(* ---------- Constants ---------- *)
CONSTANT N, T, F

(* ---------- Derived constants ---------- *)
VARIABLES correct, faulty, pc, received, sent

(* ---------- Message type ---------- *)
ECHO == "ECHO"

(* ---------- Helper definitions ---------- *)
MsgType == {ECHO}
Messages == { [mtype |-> ECHO, from |-> i] : i \in 1..N }

Process == 1..N

(* ---------- Initial state ---------- *)
Init ==
  /\ correct = { i \in Process : i > F }      \* any nondet partition, here choose first N-F as correct
  /\ faulty = Process \ correct
  /\ pc = [i \in Process |-> 
            IF i \in correct THEN 
                IF i \in faulty THEN "faulty"
                ELSE "no_init"
            ELSE "faulty"]
  /\ received = [i \in Process |-> {}]
  /\ sent = {}

(* ---------- Actions ---------- *)

(* A correct process may receive any subset of messages that have been sent by correct or Byzantine *)
Receive(i) ==
  /\ i \in correct
  /\ LET newMsgs == { m \in sent : m \notin received[i] } IN
     received' = [received EXCEPT ![i] = received[i] \cup newMsgs]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

(* Correct process that has the INIT (modeled as pc = "has_init") immediately sends ECHO and accepts *)
InitSendEcho(i) ==
  /\ i \in correct
  /\ pc[i] = "has_init"
  /\ LET echoMsg == [mtype |-> ECHO, from |-> i] IN
     sent' = sent \cup {echoMsg}
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, received>>

(* Correct process without INIT that has not yet sent ECHO, receives at least N-2T distinct ECHOs, sends ECHO *)
ThresholdSend(i, thresh) ==
  /\ i \in correct
  /\ pc[i] = "no_init"
  /\ \E S \subseteq { m \in received[i] : m.mtype = ECHO } :
        Cardinality(S) >= thresh
  /\ LET echoMsg == [mtype |-> ECHO, from |-> i] IN
     sent' = sent \cup {echoMsg}
  /\ pc' = [pc EXCEPT ![i] = "echo_sent"]
  /\ UNCHANGED <<correct, faulty, received>>

(* Correct process without INIT, receives at least N-T distinct ECHOs, sends ECHO and accepts *)
AcceptAfterThreshold(i) ==
  /\ i \in correct
  /\ pc[i] = "no_init"
  /\ \E S \subseteq { m \in received[i] : m.mtype = ECHO } :
        Cardinality(S) >= N - T
  /\ LET echoMsg == [mtype |-> ECHO, from |-> i] IN
     sent' = sent \cup {echoMsg}
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, received>>

(* Already sent ECHO, now receives >= N-T distinct ECHOs and accepts *)
AcceptIfEchoes(i) ==
  /\ i \in correct
  /\ pc[i] = "echo_sent"
  /\ \E S \subseteq { m \in received[i] : m.mtype = ECHO } :
        Cardinality(S) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, received, sent>>

(* Byzantine processes can send arbitrary ECHO messages *)
ByzSend(i) ==
  /\ i \in faulty
  /\ \E b \in Process :
        LET bogus == [mtype |-> ECHO, from |-> b] IN
        sent' = sent \cup {bogus}
  /\ UNCHANGED <<correct, faulty, pc, received>>

(* Next relation: disjunction of all possible steps *)
Next ==
  \/ \E i \in correct : Receive(i)
  \/ \E i \in correct : InitSendEcho(i)
  \/ \E i \in correct : ThresholdSend(i, N - 2*T)
  \/ \E i \in correct : AcceptAfterThreshold(i)
  \/ \E i \in correct : AcceptIfEchoes(i)
  \/ \E i \in faulty : ByzSend(i)

(* ---------- Specification ---------- *)
Spec == Init /\ [][Next]_<<correct, faulty, pc, received, sent>>

(* ---------- Type correctness invariant ---------- *)
TypeOK ==
  /\ correct \subseteq Process
  /\ faulty = Process \ correct
  /\ pc \in [Process -> {"no_init", "has_init", "echo_sent", "accepted", "faulty"}]
  /\ received \in [Process -> SUBSET Messages]
  /\ sent \subseteq Messages

(* ---------- Unforgeability constraint ---------- *)
FCConstraints ==
  /\ \A i \in correct : pc[i] # "accepted"

(* ---------- Temporal properties ---------- *)

(* If any correct process accepted, eventually all correct processes accept *)
RelayLtl ==
  []( \E i \in correct : pc[i] = "accepted" => <> \A j \in correct : pc[j] = "accepted" )

(* If all correct processes started with INIT (modeled as "has_init"), eventually all accept *)
CorrLtl ==
  ( \A i \in correct : pc[i] = "has_init" ) => []<>( \A j \in correct : pc[j] = "accepted" )

(* Unforgeability as a temporal property: if no correct process started with INIT, then never any accept *)
UnforgLtl ==
  ( \A i \in correct : pc[i] = "no_init" ) => [] ( \A j \in correct : pc[j] # "accepted" )

====