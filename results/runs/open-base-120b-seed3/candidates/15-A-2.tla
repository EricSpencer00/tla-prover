---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F

(* ------------------------------------------------------------------- *)
(*   Process and Message definitions                                   *)
(* ------------------------------------------------------------------- *)

Proc == 1..N

Message == [type : {"ECHO"}, sender : Proc]

(* ------------------------------------------------------------------- *)
(*   Variables                                                         *)
(* ------------------------------------------------------------------- *)

VARIABLES Correct, Faulty, InitSet, pc, recvd, Sent

vars == <<Correct, Faulty, InitSet, pc, recvd, Sent>>

(* ------------------------------------------------------------------- *)
(*   Helper definitions                                                *)
(* ------------------------------------------------------------------- *)

EchoSenders(p) == { m.sender : m \in recvd[p] }
EchoCount(p)   == Cardinality(EchoSenders(p))

(* ------------------------------------------------------------------- *)
(*   Initialization                                                     *)
(* ------------------------------------------------------------------- *)

Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ InitSet \subseteq Correct
  /\ pc = [p \in Proc |-> IF p \in Correct THEN
                         IF p \in InitSet THEN "Init" ELSE "None"
                       ELSE "None"]
  /\ recvd = [p \in Proc |-> {}]
  /\ Sent = {}

(* ------------------------------------------------------------------- *)
(*   Actions                                                            *)
(* ------------------------------------------------------------------- *)

(* A correct process that started with the INIT message immediately
   sends an ECHO and accepts.                                          *)
InitAction(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ Sent' = Sent \/ {[type |-> "ECHO", sender |-> p]}
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, InitSet, recvd>>

(* Receive any (possibly forged) set of messages. *)
Receive(p) ==
  /\ p \in Correct
  /\ \E new \subseteq Message :
        /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, InitSet, pc, Sent>>

(* Send an ECHO when having seen enough distinct ECHO messages,
   but not enough to accept yet.                                       *)
SendEcho(p) ==
  /\ p \in Correct
  /\ pc[p] \in {"None", "Init"}   \* not yet accepted
  /\ EchoCount(p) >= N - 2*T
  /\ EchoCount(p) <  N - T
  /\ Sent' = Sent \/ {[type |-> "ECHO", sender |-> p]}
  /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED <<Correct, Faulty, InitSet, recvd>>

(* Send an ECHO and accept when the strong threshold is reached. *)
SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] # "Accepted"
  /\ EchoCount(p) >= N - T
  /\ Sent' = Sent \/ {[type |-> "ECHO", sender |-> p]}
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, InitSet, recvd>>

(* Accept after having already sent an ECHO and now reaching the strong
   threshold.                                                          *)
AcceptOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ EchoCount(p) >= N - T
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, InitSet, recvd, Sent>>

(* ------------------------------------------------------------------- *)
(*   Combined step for a process                                        *)
(* ------------------------------------------------------------------- *)

ProcStep(p) ==
  InitAction(p) \/ SendEcho(p) \/ SendEchoAndAccept(p) \/ AcceptOnly(p) \/ Receive(p)

(* ------------------------------------------------------------------- *)
(*   Next relation                                                      *)
(* ------------------------------------------------------------------- *)

Next ==
  \/ \E p \in Correct : ProcStep(p)

(* ------------------------------------------------------------------- *)
(*   Fairness condition                                                 *)
(* ------------------------------------------------------------------- *)

Fairness == \A p \in Correct : WF_vars(ProcStep(p))

(* ------------------------------------------------------------------- *)
(*   Specification                                                      *)
(* ------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars /\ Fairness

(* ------------------------------------------------------------------- *)
(*   Type invariants                                                    *)
(* ------------------------------------------------------------------- *)

TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ InitSet \subseteq Correct
  /\ pc \in [Proc -> {"None","Init","EchoSent","Accepted"}]
  /\ \A p \in Proc : recvd[p] \subseteq Message
  /\ Sent \subseteq Message

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* ------------------------------------------------------------------- *)
(*   LTL properties                                                     *)
(* ------------------------------------------------------------------- *)

CorrLtl ==
  [] ( (InitSet = Correct) => <> ( \A p \in Correct : pc[p] = "Accepted") )

RelayLtl ==
  [] ( ( \E p \in Correct : pc[p] = "Accepted") => <> ( \A q \in Correct : pc[q] = "Accepted") )

UnforgLtl ==
  [] ( (InitSet = {}) => [] ( \A p \in Correct : pc[p] # "Accepted") )

(* ------------------------------------------------------------------- *)
(*   Exported identifiers                                               *)
(* ------------------------------------------------------------------- *)

THEOREM SpecImpliesTypeOK == Spec => []TypeOK

====