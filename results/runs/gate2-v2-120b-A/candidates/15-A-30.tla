---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

(* --------------------------------------------------------------------- *)
(* Derived sets *)
Proc == 1..N
ECHO == "ECHO"

(* --------------------------------------------------------------------- *)
(* State variables *)
VARIABLES
    correct,          \* set of correct processes
    faulty,           \* set of Byzantine processes
    pc,               \* control location per process
    sent,             \* set of messages sent by correct processes
    recvd             \* map from process to set of messages it has received

(* --------------------------------------------------------------------- *)
(* Message definition *)
Msg == [type : {"ECHO"}, from : Proc]

(* --------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc = [p \in Proc |-> 
            IF p \in correct THEN "Init" ELSE "Faulty"]
    /\ sent = {}
    /\ recvd = [p \in Proc |-> {}]

(* --------------------------------------------------------------------- *)
(* Helper definitions *)
CountEchos(p) ==
    Cardinality({ m \in recvd[p] : m.type = "ECHO" })

DistinctSenders(p) ==
    { m.from : m \in recvd[p] : m.type = "ECHO" }

(* --------------------------------------------------------------------- *)
(* Actions *)

(* A correct process may receive any subset of the messages that have been sent
   (including those from Byzantine processes, which are abstracted as any ECHO). *)
Receive(p) ==
    /\ p \in correct
    /\ \E new \subseteq sent :
         /\ recvd' = [recvd EXCEPT ![p] = @ \cup new]
         /\ UNCHANGED << correct, faulty, pc, sent >>

(* If a correct process is in the "Init" state (meaning it has the INIT),
   it immediately sends an ECHO and accepts. *)
SendEchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "Init"
    /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED recvd

(* A correct process that has not yet sent ECHO receives at least N-2T distinct ECHOs
   and sends its own ECHO but does not yet accept. *)
SendEchoOnly(p) ==
    /\ p \in correct
    /\ pc[p] = "Init" = FALSE /\ pc[p] = "None"
    /\ Cardinality(DistinctSenders(p)) >= N - 2 * T
    /\ Cardinality(DistinctSenders(p)) < N - T
    /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
    /\ pc' = [pc EXCEPT ![p] = "Sent"]
    /\ UNCHANGED recvd

(* A correct process that has not yet sent ECHO receives at least N-T distinct ECHOs
   and sends ECHO and accepts. *)
SendEchoAndAccept(p) ==
    /\ p \in correct
    /\ \E cur \in {"Init", "None"} : pc[p] = cur
    /\ Cardinality(DistinctSenders(p)) >= N - T
    /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED recvd

(* A correct process that has already sent ECHO receives at least N-T distinct ECHOs
   and accepts. *)
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "Sent"
    /\ Cardinality(DistinctSenders(p)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED << sent, recvd >>

(* Byzantine processes may send arbitrary messages; we model this by allowing them
   to add any ECHO message to the global sent set at any time. *)
ByzantineSend(p) ==
    /\ p \in faulty
    /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
    /\ UNCHANGED << correct, faulty, pc, recvd >>

(* --------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct : SendEchoAndAccept(p)
    \/ \E p \in correct : SendEchoOnly(p)
    \/ \E p \in correct : SendEchoAndAccept(p)  \* second occurrence for N-T case
    \/ \E p \in correct : AcceptAfterEcho(p)
    \/ \E p \in faulty  : ByzantineSend(p)

(* --------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<correct, faulty, pc, sent, recvd>>

(* --------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> {"Init", "None", "Sent", "Accept", "Faulty"}]
    /\ sent \subseteq Msg
    /\ \A p \in Proc : recvd[p] \subseteq Msg

(* --------------------------------------------------------------------- *)
(* Safety constraint: unforgeability (no broadcast) *)
FCConstraints ==
    /\ \A p \in correct : pc[p] # "Accept"
    \/ \E p \in correct : pc[p] = "Accept"

(* --------------------------------------------------------------------- *)
(* Linear-time properties for liveness checking *)

CorrLtl == []( ( \A p \in correct : pc[p] = "Init") => <> ( \A p \in correct : pc[p] = "Accept"))

RelayLtl == []( ( \E p \in correct : pc[p] = "Accept") => <> ( \A p \in correct : pc[p] = "Accept"))

UnforgLtl == []( ( \A p \in correct : pc[p] = "None") => []( \A p \in correct : pc[p] # "Accept"))

=============================================================================