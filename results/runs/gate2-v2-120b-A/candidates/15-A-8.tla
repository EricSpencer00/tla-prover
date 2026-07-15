---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, T, F

(* ------------------------------------------------------------------------- *)
(* Derived sets *)
(* ------------------------------------------------------------------------- *)
PROC == 0..(N-1)

MessageType == {"ECHO"}
Message == [type : MessageType, from : PROC]

(* ------------------------------------------------------------------------- *)
(* Variables *)
(* ------------------------------------------------------------------------- *)
VARIABLES
    correct,          \* set of correct processes
    faulty,           \* set of Byzantine processes
    pc,               \* control location per process
    received,         \* set of messages received per process
    sent               \* set of messages sent by correct processes

(* ------------------------------------------------------------------------- *)
(* Control locations *)
(* ------------------------------------------------------------------------- *)
InitState    == "Init"
NonInitState == "NonInit"
EchoSent     == "EchoSent"
Accepted     == "Accepted"

(* ------------------------------------------------------------------------- *)
(* Helper definitions *)
(* ------------------------------------------------------------------------- *)
SentSet(p) == { m \in sent : m.from = p }

DistinctSenders(S) == { m.from : m \in S }

IsECHO(m) == m.type = "ECHO"

(* ------------------------------------------------------------------------- *)
(* Initialization *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ correct \subseteq PROC
    /\ faulty = PROC \ correct
    /\ Cardinality(correct) = N - F
    /\ pc = [p \in PROC |-> 
                IF p \in correct THEN InitState ELSE InitState]
    /\ received = [p \in PROC |-> {}]
    /\ sent = {}

(* ------------------------------------------------------------------------- *)
(* Actions *)
(* ------------------------------------------------------------------------- *)

(* A correct process receives any subset of messages that have been sent
   by correct processes and any arbitrary messages from Byzantine processes. *)
Receive(p) ==
    /\ p \in correct
    /\ \E newMsgs \subseteq 
          { m \in Message : 
                (m.from \in correct /\ m \in sent) \/ 
                (m.from \in faulty) } :
          /\ received' = [received EXCEPT ![p] = received[p] \cup newMsgs]
          /\ UNCHANGED <<correct, faulty, pc, sent>>

(* When a process is in InitState, it immediately sends an ECHO and accepts. *)
BroadcastEchoAccept(p) ==
    /\ pc[p] = InitState
    /\ LET echo == [type |-> "ECHO", from |-> p] IN
       /\ sent' = sent \cup {echo}
       /\ received' = [received EXCEPT ![p] = received[p] \cup {echo}]
       /\ pc' = [pc EXCEPT ![p] = Accepted]

(* If a process has not yet sent ECHO and receives >= N-2T distinct ECHO
   messages (but fewer than N-T), it sends ECHO but does not accept. *)
SendEchoNoAccept(p) ==
    /\ pc[p] = InitState
    /\ LET echos == { m \in received[p] : IsECHO(m) } IN
       /\ Cardinality(DistinctSenders(echos)) >= N - 2 * T
       /\ Cardinality(DistinctSenders(echos)) < N - T
       /\ LET echo == [type |-> "ECHO", from |-> p] IN
          /\ sent' = sent \cup {echo}
          /\ received' = [received EXCEPT ![p] = received[p] \cup {echo}]
          /\ pc' = [pc EXCEPT ![p] = EchoSent]

(* If a process has not yet sent ECHO and receives >= N-T distinct ECHO
   messages, it sends ECHO and accepts. *)
SendEchoAndAccept(p) ==
    /\ pc[p] = InitState
    /\ LET echos == { m \in received[p] : IsECHO(m) } IN
       /\ Cardinality(DistinctSenders(echos)) >= N - T
       /\ LET echo == [type |-> "ECHO", from |-> p] IN
          /\ sent' = sent \cup {echo}
          /\ received' = [received EXCEPT ![p] = received[p] \cup {echo}]
          /\ pc' = [pc EXCEPT ![p] = Accepted]

(* A process that has already sent ECHO accepts upon receiving >= N-T ECHO. *)
AcceptAfterEcho(p) ==
    /\ pc[p] = EchoSent
    /\ LET echos == { m \in received[p] : IsECHO(m) } IN
       /\ Cardinality(DistinctSenders(echos)) >= N - T
       /\ pc' = [pc EXCEPT ![p] = Accepted]

(* ------------------------------------------------------------------------- *)
(* Next-state relation *)
(* ------------------------------------------------------------------------- *)
Next ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct : BroadcastEchoAccept(p)
    \/ \E p \in correct : SendEchoNoAccept(p)
    \/ \E p \in correct : SendEchoAndAccept(p)
    \/ \E p \in correct : AcceptAfterEcho(p)

(* ------------------------------------------------------------------------- *)
(* Specification *)
(* ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<correct, faulty, pc, received, sent>>

(* ------------------------------------------------------------------------- *)
(* Invariant: Type correctness *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
    /\ correct \subseteq PROC
    /\ faulty = PROC \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [PROC -> {"Init", "NonInit", "EchoSent", "Accepted"}]
    /\ received \in [PROC -> SUBSET Message]
    /\ sent \subseteq Message
    /\ \A m \in sent : IsECHO(m) /\ m.from \in correct

(* ------------------------------------------------------------------------- *)
(* Invariant: Unforgeability (no correct process ever accepts if none started in InitState) *)
(* ------------------------------------------------------------------------- *)
NoBroadcastInit ==
    /\ \A p \in correct : pc[p] # Accepted

FCConstraints ==
    NoBroadcastInit

(* ------------------------------------------------------------------------- *)
(* Liveness properties (expressed as state predicates for TLAPS) *)
(* ------------------------------------------------------------------------- *)

(* All correct processes eventually accept when they all started with INIT. *)
CorrLtl ==
    \A p \in correct : <> (pc[p] = Accepted)

(* If any correct process accepts, eventually all correct processes accept. *)
RelayLtl ==
    (\E p \in correct : <> (pc[p] = Accepted)) => 
        (\A p \in correct : <> (pc[p] = Accepted))

(* Unforgeability expressed as a temporal property (for completeness). *)
UnforgLtl ==
    [] NoBroadcastInit

====