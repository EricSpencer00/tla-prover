---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* ------------------------------------------------------------------------- *)
(* Process set and message definition                                         *)
(* ------------------------------------------------------------------------- *)

Proc == 1..N

Message == [sender : Proc, type : {"ECHO"}]

EchoMsg(p) == [sender |-> p, type |-> "ECHO"]

VARIABLES Correct, Faulty, sent, recv, pc

vars == <<Correct, Faulty, sent, recv, pc>>

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                         *)
(* ------------------------------------------------------------------------- *)

ByzMsgs == { [sender |-> b, type |-> "ECHO"] : b \in Faulty }

(* Set of distinct senders of ECHO messages that p has received *)
EchoSenders(p) ==
  { s \in Proc :
      \E m \in recv[p] :
        /\ m.type = "ECHO"
        /\ m.sender = s }

EchoCount(p) == Cardinality(EchoSenders(p))

(* ------------------------------------------------------------------------- *)
(* Initial state                                                              *)
(* ------------------------------------------------------------------------- *)

Init ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ Cardinality(Correct) = N - F
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ \E initRecv \in [Correct -> BOOLEAN] :
        /\ pc = [p \in Proc |->
                IF p \in Correct
                THEN IF initRecv[p] THEN "Init" ELSE "NoInit"
                ELSE "NoInit"]

(* ------------------------------------------------------------------------- *)
(* Receive action (nondeterministic delivery of messages)                     *)
(* ------------------------------------------------------------------------- *)

Receive(p) ==
  /\ p \in Correct
  /\ \E new \in SUBSET ((sent \cup ByzMsgs) \ recv[p]) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, sent, pc>>

(* ------------------------------------------------------------------------- *)
(* Act action (send ECHO, possibly accept)                                    *)
(* ------------------------------------------------------------------------- *)

Act(p) ==
  \/ /\ p \in Correct
     /\ pc[p] = "Init"
     /\ pc' = [pc EXCEPT ![p] = "Accept"]
     /\ sent' = sent \cup { EchoMsg(p) }
     /\ UNCHANGED <<Correct, Faulty, recv>>
  \/ /\ p \in Correct
     /\ pc[p] = "NoInit"
     /\ EchoCount(p) >= N - T
     /\ pc' = [pc EXCEPT ![p] = "Accept"]
     /\ sent' = sent \cup { EchoMsg(p) }
     /\ UNCHANGED <<Correct, Faulty, recv>>
  \/ /\ p \in Correct
     /\ pc[p] = "NoInit"
     /\ EchoCount(p) >= N - 2 * T
     /\ EchoCount(p) < N - T
     /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
     /\ sent' = sent \cup { EchoMsg(p) }
     /\ UNCHANGED <<Correct, Faulty, recv>>
  \/ /\ p \in Correct
     /\ pc[p] = "EchoSent"
     /\ EchoCount(p) >= N - T
     /\ pc' = [pc EXCEPT ![p] = "Accept"]
     /\ UNCHANGED <<Correct, Faulty, sent, recv>>

(* ------------------------------------------------------------------------- *)
(* Next-state relation                                                       *)
(* ------------------------------------------------------------------------- *)

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : Act(p)

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Invariants                                                                 *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ Cardinality(Correct) = N - F
  /\ sent \subseteq { EchoMsg(q) : q \in Correct }
  /\ recv \in [Proc -> SUBSET { EchoMsg(q) : q \in Proc }]
  /\ pc \in [Proc -> {"NoInit","Init","EchoSent","Accept"}]

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* ------------------------------------------------------------------------- *)
(* Liveness properties                                                       *)
(* ------------------------------------------------------------------------- *)

CorrLtl == [] ( ( \A p \in Correct : pc[p] = "Init" ) => <> ( \A p \in Correct : pc[p] = "Accept" ) )

RelayLtl == [] ( ( \E p \in Correct : pc[p] = "Accept" ) => <> ( \A p \in Correct : pc[p] = "Accept" ) )

UnforgLtl == [] ( ( \A p \in Correct : pc[p] = "NoInit" ) => [] ( \A p \in Correct : pc[p] # "Accept" ) )
====