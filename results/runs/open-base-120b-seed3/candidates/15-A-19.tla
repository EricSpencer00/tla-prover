---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* --------------------------------------------------------------------- *)
(*   Basic definitions                                                   *)
(* --------------------------------------------------------------------- *)

Proc == 1..N

Msg == [sender : Proc, type : {"ECHO"}]

(* --------------------------------------------------------------------- *)
(*   Variables                                                          *)
(* --------------------------------------------------------------------- *)

VARIABLES Correct, Faulty, pc, recv, sent

vars == <<Correct, Faulty, pc, recv, sent>>

(* --------------------------------------------------------------------- *)
(*   Helper functions                                                    *)
(* --------------------------------------------------------------------- *)

ReceivedEchoSenders(p) == { m.sender : m \in recv[p] }

EchoCount(p) == Cardinality(ReceivedEchoSenders(p))

ByzantineMsgs == { [sender |-> f, type |-> "ECHO"] : f \in Faulty }

PossibleMsgs == sent \cup ByzantineMsgs

EchoMsg(p) == [sender |-> p, type |-> "ECHO"]

(* --------------------------------------------------------------------- *)
(*   Initial state                                                      *)
(* --------------------------------------------------------------------- *)

Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"NoInit", "Init", "EchoSent", "Accepted"}]
  /\ \A p \in Proc :
        IF p \in Correct
        THEN pc[p] \in {"NoInit", "Init"}
        ELSE pc[p] = "NoInit"
  /\ recv \in [Proc -> SUBSET Msg]
  /\ \A p \in Proc : recv[p] = {}
  /\ sent = {}

(* --------------------------------------------------------------------- *)
(*   Actions                                                            *)
(* --------------------------------------------------------------------- *)

(* 1. Receive arbitrary set of messages (including Byzantine ones) *)
Receive ==
  \E p \in Correct :
    \E new \subseteq PossibleMsgs :
      /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
      /\ UNCHANGED <<Correct, Faulty, pc, sent>>

(* 2. Immediate accept and echo after having the INIT *)
SendEchoImmediate ==
  \E p \in Correct :
    /\ pc[p] = "Init"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { EchoMsg(p) }
    /\ UNCHANGED <<Correct, Faulty, recv>>

(* 3. Send ECHO when enough echoes received, but not enough to accept *)
SendEchoWhenEnough ==
  \E p \in Correct :
    /\ pc[p] = "NoInit"
    /\ EchoMsg(p) \notin sent
    /\ EchoCount(p) >= N - 2*T
    /\ EchoCount(p) <  N - T
    /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
    /\ sent' = sent \cup { EchoMsg(p) }
    /\ UNCHANGED <<Correct, Faulty, recv>>

(* 4. Send ECHO and accept when threshold reached *)
SendEchoAndAcceptWhenEnough ==
  \E p \in Correct :
    /\ pc[p] = "NoInit"
    /\ EchoMsg(p) \notin sent
    /\ EchoCount(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { EchoMsg(p) }
    /\ UNCHANGED <<Correct, Faulty, recv>>

(* 5. Accept after having already sent ECHO and now enough echoes *)
AcceptAfterEcho ==
  \E p \in Correct :
    /\ pc[p] = "EchoSent"
    /\ EchoCount(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<Correct, Faulty, recv, sent>>

Next ==
  \/ Receive
  \/ SendEchoImmediate
  \/ SendEchoWhenEnough
  \/ SendEchoAndAcceptWhenEnough
  \/ AcceptAfterEcho

(* --------------------------------------------------------------------- *)
(*   Specification                                                      *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(*   Invariants                                                         *)
(* --------------------------------------------------------------------- *)

TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"NoInit", "Init", "EchoSent", "Accepted"}]
  /\ \A p \in Proc :
        IF p \in Correct
        THEN pc[p] \in {"NoInit", "Init", "EchoSent", "Accepted"}
        ELSE pc[p] = "NoInit"
  /\ recv \in [Proc -> SUBSET Msg]
  /\ sent \subseteq Msg

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* --------------------------------------------------------------------- *)
(*   LTL properties                                                     *)
(* --------------------------------------------------------------------- *)

CorrLtl ==
  ( \A p \in Correct : pc[p] = "Init" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl ==
  ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl ==
  ( \A p \in Correct : pc[p] = "NoInit" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

====