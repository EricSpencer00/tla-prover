---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* ------------------------------------------------------------------------ *)
(* Derived sets and types                                                    *)
(* ------------------------------------------------------------------------ *)

Proc == 1..N

Message == [type : {"ECHO"}, sender : Proc]

(* ------------------------------------------------------------------------ *)
(* Variables                                                                 *)
(* ------------------------------------------------------------------------ *)

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

(* ------------------------------------------------------------------------ *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------ *)

Senders(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }
Cnt(p)     == Cardinality(Senders(p))

AllByzMsgs == { [type |-> "ECHO", sender |-> f] : f \in faulty }
AllMessages == sent \cup AllByzMsgs

(* ------------------------------------------------------------------------ *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------ *)

Init ==
  /\ correct \subseteq Proc
  /\ Cardinality(correct) = N - F
  /\ faulty = Proc \ correct
  /\ pc \in [Proc -> {"Init0", "Init1", "EchoSent", "Accepted"}]
  /\ \A p \in Proc :
        IF p \in correct
        THEN pc[p] \in {"Init0", "Init1"}
        ELSE pc[p] = "Init0"
  /\ recv = [p \in Proc |-> {}]
  /\ sent = {}

(* ------------------------------------------------------------------------ *)
(* Receive action (a correct process may receive any new messages)          *)
(* ------------------------------------------------------------------------ *)

Receive(p) ==
  /\ p \in correct
  /\ \E new \in SUBSET (AllMessages \ recv[p]) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<correct, faulty, pc, sent>>

(* ------------------------------------------------------------------------ *)
(* Act action (a correct process may send ECHO and/or accept)               *)
(* ------------------------------------------------------------------------ *)

Act(p) ==
  LET s == Senders(p) IN
  LET c == Cardinality(s) IN
    \/ /\ pc[p] = "Init1"
        /\ pc' = [pc EXCEPT ![p] = "Accepted"]
        /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
        /\ UNCHANGED <<correct, faulty, recv>>
    \/ /\ pc[p] = "Init0" /\ c >= N - T
        /\ pc' = [pc EXCEPT ![p] = "Accepted"]
        /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
        /\ UNCHANGED <<correct, faulty, recv>>
    \/ /\ pc[p] = "Init0" /\ c >= N - 2*T /\ c < N - T
        /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
        /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
        /\ UNCHANGED <<correct, faulty, recv>>
    \/ /\ pc[p] = "EchoSent" /\ c >= N - T
        /\ pc' = [pc EXCEPT ![p] = "Accepted"]
        /\ UNCHANGED <<correct, faulty, recv, sent>>
    \/ /\ UNCHANGED <<correct, faulty, pc, recv, sent>>

(* ------------------------------------------------------------------------ *)
(* Next-state relation                                                      *)
(* ------------------------------------------------------------------------ *)

Next ==
  \/ \E p \in correct: Receive(p)
  \/ \E p \in correct: Act(p)

(* ------------------------------------------------------------------------ *)
(* Specification                                                             *)
(* ------------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------ *)
(* Invariants                                                                *)
(* ------------------------------------------------------------------------ *)

TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty = Proc \ correct
  /\ pc \in [Proc -> {"Init0","Init1","EchoSent","Accepted"}]
  /\ recv \in [Proc -> SUBSET Message]
  /\ sent \subseteq Message
  /\ \A m \in sent : m.type = "ECHO" /\ m.sender \in correct

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F

(* ------------------------------------------------------------------------ *)
(* LTL properties                                                            *)
(* ------------------------------------------------------------------------ *)

CorrLtl ==
  [] ( ( \A p \in correct : pc[p] = "Init1")
        => <> ( \A p \in correct : pc[p] = "Accepted") )

RelayLtl ==
  [] ( ( \E p \in correct : pc[p] = "Accepted")
        => <> ( \A p \in correct : pc[p] = "Accepted") )

UnforgLtl ==
  [] ( ( \A p \in correct : pc[p] = "Init0")
        => [] ( \A p \in correct : pc[p] # "Accepted") )

====