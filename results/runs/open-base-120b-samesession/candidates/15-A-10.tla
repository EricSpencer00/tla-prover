---- MODULE bcastByz ----
EXTENDS Naturals, TLC

CONSTANTS N, T, F

(* ------------------------------------------------------------------- *)
(*   Sets and basic definitions                                         *)
(* ------------------------------------------------------------------- *)

Proc == 1 .. N

PcVals == {"Start0", "Start1", "EchoSent", "Accepted"}

Msg == [sender : Proc, t : {"ECHO"}]

EchoMsg(p) == [sender |-> p, t |-> "ECHO"]

(* ------------------------------------------------------------------- *)
(*   Variables                                                          *)
(* ------------------------------------------------------------------- *)

VARIABLES
    correct,        \* set of correct processes
    faulty,         \* set of Byzantine processes
    pc,             \* control location of each process
    recv,           \* messages received by each process
    sent,           \* set of ECHO messages sent by correct processes
    initReceived    \* subset of correct processes that start with INIT

(* ------------------------------------------------------------------- *)
(*   Initial state                                                      *)
(* ------------------------------------------------------------------- *)

Init ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ faulty = Proc \ correct
    /\ sent = {}
    /\ \A p \in Proc : pc[p] \in {"Start0", "Start1"}
    /\ initReceived = { p \in correct : pc[p] = "Start1" }
    /\ \A p \in Proc : recv[p] = {}

(* ------------------------------------------------------------------- *)
(*   One-step action for a correct process                              *)
(* ------------------------------------------------------------------- *)

ProcStep(p) ==
    /\ p \in correct
    /\ LET possibleMsgs == sent \cup { EchoMsg(s) : s \in faulty } IN
       /\ newMsgs \subseteq possibleMsgs \ recv[p]
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
    /\ LET echoSenders == { m.sender : m \in recv'[p] } IN
       /\ CASE
            pc[p] = "Start1" ->
                /\ pc' = [pc EXCEPT ![p] = "Accepted"]
                /\ sent' = sent \cup { EchoMsg(p) }
            pc[p] = "Start0" /\ Cardinality(echoSenders) >= N - 2 * T
                               /\ Cardinality(echoSenders) < N - T ->
                /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
                /\ sent' = sent \cup { EchoMsg(p) }
            pc[p] = "Start0" /\ Cardinality(echoSenders) >= N - T ->
                /\ pc' = [pc EXCEPT ![p] = "Accepted"]
                /\ sent' = sent \cup { EchoMsg(p) }
            pc[p] = "EchoSent" /\ Cardinality(echoSenders) >= N - T ->
                /\ pc' = [pc EXCEPT ![p] = "Accepted"]
                /\ UNCHANGED sent
            OTHER ->
                /\ pc' = pc
                /\ UNCHANGED sent
          ENDCASE
    /\ UNCHANGED << correct, faulty, initReceived >>

(* ------------------------------------------------------------------- *)
(*   Next-state relation                                                *)
(* ------------------------------------------------------------------- *)

Next == \E p \in Proc : ProcStep(p)

vars == << correct, faulty, pc, recv, sent, initReceived >>

(* ------------------------------------------------------------------- *)
(*   Specification (with weak fairness)                                 *)
(* ------------------------------------------------------------------- *)

Spec ==
    Init /\ [][Next]_vars /\ \A p \in correct : WF_vars(ProcStep(p))

(* ------------------------------------------------------------------- *)
(*   Invariants                                                         *)
(* ------------------------------------------------------------------- *)

TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ pc \in [Proc -> PcVals]
    /\ recv \in [Proc -> SUBSET Msg]
    /\ sent \subseteq { EchoMsg(p) : p \in correct }
    /\ initReceived \subseteq correct

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F

(* ------------------------------------------------------------------- *)
(*   Temporal properties                                                *)
(* ------------------------------------------------------------------- *)

CorrLtl == (initReceived = correct) => <> ( \A p \in correct : pc[p] = "Accepted" )

RelayLtl == <> ( \E p \in correct : pc[p] = "Accepted" ) => <> ( \A p \in correct : pc[p] = "Accepted" )

UnforgLtl == (initReceived = {}) => [] ( \A p \in correct : pc[p] # "Accepted" )

====