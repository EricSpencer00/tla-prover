---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N, T, F

(* ------------------------------------------------------------------------- *)
(* Derived sets and basic definitions                                        *)
(* ------------------------------------------------------------------------- *)

MessageType == {"ECHO"}

Message == [type : MessageType, from : 1..N]

(* Control locations for each process *)
CtrlLoc == {"NoInit", "HasInit", "SentEcho", "Accepted"}

VARIABLES correct, faulty, pc, sent, rcvd

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                        *)
(* ------------------------------------------------------------------------- *)

InitPartitions ==
  (* N > 3T and T >= F are assumed in the cfg; we do not enforce them here. *)
  \E wrong \in SUBSET 1..N :
    /\ Cardinality(wrong) = F
    /\ correct = 1..N \ wrong
    /\ faulty = wrong

InitPc ==
  [p \in 1..N |-> IF p \in correct THEN "NoInit" ELSE "NoInit"]

InitSent ==
  {}

InitRcvd ==
  [p \in 1..N |-> {}]

(* ------------------------------------------------------------------------- *)
(* Initial state                                                             *)
(* ------------------------------------------------------------------------- *)

Init ==
  /\ InitPartitions
  /\ pc = InitPc
  /\ sent = InitSent
  /\ rcvd = InitRcvd

(* ------------------------------------------------------------------------- *)
(* Actions                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Correct process receives a non‑empty set of messages that have been sent *)
Receive(p) ==
  /\ p \in correct
  /\ \E new \subseteq sent :
        /\ new # {}
        /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup new]
        /\ UNCHANGED << pc, sent, correct, faulty >>

SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] \in {"HasInit", "SentEcho"}
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ UNCHANGED << pc, rcvd, correct, faulty >>

(* Transition to HasInit state: the process is considered to have received INIT *)
GetInit(p) ==
  /\ p \in correct
  /\ pc[p] = "NoInit"
  /\ pc' = [pc EXCEPT ![p] = "HasInit"]
  /\ UNCHANGED << sent, rcvd, correct, faulty >>

(* Sending ECHO without acceptance *)
SendEchoOnly(p) ==
  /\ p \in correct
  /\ pc[p] = "NoInit"
  /\ \E echoSenders \subseteq correct :
        /\ Cardinality(echoSenders) >= (N - 2 * T)
        /\ echoSenders # {}
        /\ \A q \in echoSenders : [type |-> "ECHO", from |-> q] \in rcvd[p]
        /\ pc' = [pc EXCEPT ![p] = "SentEcho"]
        /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
        /\ UNCHANGED << rcvd, correct, faulty >>

(* Sending ECHO and accepting *)
SendEchoAndAccept(p) ==
  /\ p \in correct
  /\ pc[p] \in {"NoInit", "SentEcho"}
  /\ \E echoSenders \subseteq correct :
        /\ Cardinality(echoSenders) >= (N - T)
        /\ \A q \in echoSenders : [type |-> "ECHO", from |-> q] \in rcvd[p]
        /\ pc' = [pc EXCEPT ![p] = "Accepted"]
        /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
        /\ UNCHANGED << rcvd, correct, faulty >>

(* Accept after already having sent ECHO *)
AcceptAfterEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "SentEcho"
  /\ \E echoSenders \subseteq correct :
        /\ Cardinality(echoSenders) >= (N - T)
        /\ \A q \in echoSenders : [type |-> "ECHO", from |-> q] \in rcvd[p]
        /\ pc' = [pc EXCEPT ![p] = "Accepted"]
        /\ UNCHANGED << sent, rcvd, correct, faulty >>

(* Byzantine processes may send arbitrary messages *)
ByzSend(p) ==
  /\ p \in faulty
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ UNCHANGED << pc, rcvd, correct, faulty >>

(* ------------------------------------------------------------------------- *)
(* Next-state relation                                                       *)
(* ------------------------------------------------------------------------- *)

Next ==
  \/ \E p \in correct : Receive(p)
  \/ \E p \in correct : GetInit(p)
  \/ \E p \in correct : SendEcho(p)
  \/ \E p \in correct : SendEchoOnly(p)
  \/ \E p \in correct : SendEchoAndAccept(p)
  \/ \E p \in correct : AcceptAfterEcho(p)
  \/ \E p \in faulty : ByzSend(p)

Spec == Init /\ [][Next]_<<pc, sent, rcvd, correct, faulty>>

(* ------------------------------------------------------------------------- *)
(* Type correctness invariant                                                *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty = 1..N \ correct
  /\ correct \cap faulty = {}
  /\ \A p \in 1..N : pc[p] \in CtrlLoc
  /\ sent \subseteq Message
  /\ \A p \in 1..N : rcvd[p] \subseteq Message
  /\ \A m \in sent : m.type \in MessageType
  /\ \A p \in 1..N : \A m \in rcvd[p] : m.type \in MessageType

(* ------------------------------------------------------------------------- *)
(* Safety invariant (FCConstraints)                                          *)
(* ------------------------------------------------------------------------- *)

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ N > 3 * T
  /\ T >= F

(* ------------------------------------------------------------------------- *)
(* Liveness properties (expressed as temporal formulas)                     *)
(* ------------------------------------------------------------------------- *)

CorrLtl == 
  \A p \in correct : <> (pc[p] = "Accepted")

RelayLtl == 
  (\E p \in correct : pc[p] = "Accepted") => [](\A p \in correct : pc[p] = "Accepted")

UnforgLtl == 
  (\A p \in correct : pc[p] # "HasInit") => [](\A p \in correct : pc[p] # "Accepted")

====