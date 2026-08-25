---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* --------------------------------------------------------------------- *)
(*   Process set and message definition                                   *)
(* --------------------------------------------------------------------- *)

Proc == 1 .. N

Message == [type : {"ECHO"}, sender : Proc]

(* --------------------------------------------------------------------- *)
(*   Variables                                                            *)
(* --------------------------------------------------------------------- *)

VARIABLES Correct, Faulty, pc, recv, sent

vars == << Correct, Faulty, pc, recv, sent >>

(* --------------------------------------------------------------------- *)
(*   Helper definitions                                                   *)
(* --------------------------------------------------------------------- *)

EchoSenders(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }
EchoCount(p)   == Cardinality(EchoSenders(p))

AllInit    == \A p \in Correct : pc[p] = "Init"
AllAccept  == \A p \in Correct : pc[p] = "Accept"
ExistsAccept == \E p \in Correct : pc[p] = "Accept"
AllNoInit  == \A p \in Correct : pc[p] = "NoInit"

(* --------------------------------------------------------------------- *)
(*   Initial state                                                       *)
(* --------------------------------------------------------------------- *)

Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \\ Correct
  /\ pc \in [Proc -> {"NoInit","Init","Echo","Accept"}]
  /\ \A p \in Proc : pc[p] \in {"NoInit","Init"}  \* only the two initial states
  /\ recv = [p \in Proc |-> {}]
  /\ sent = {}

(* --------------------------------------------------------------------- *)
(*   Actions                                                             *)
(* --------------------------------------------------------------------- *)

(* A correct process may receive any subset of messages that have been
   sent by correct processes or arbitrary messages that could be sent by
   Byzantine processes. *)
Receive(p) ==
  /\ p \in Correct
  /\ LET possible == sent \union
                     { [type |-> "ECHO", sender |-> f] : f \in Faulty }
         newMsgs \in SUBSET(possible \ recv[p])
     IN
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
        /\ UNCHANGED << Correct, Faulty, pc, sent >>

(* If a correct process started with the INIT message, it immediately
   sends an ECHO and accepts. *)
SendEchoFromInit(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED << Correct, Faulty, recv >>

(* A correct process that has not yet sent ECHO and has received at least
   N-2T distinct ECHO messages (but fewer than N-T) sends an ECHO but does
   not accept yet. *)
SendEchoNoAccept(p) ==
  /\ p \in Correct
  /\ pc[p] \in {"NoInit","Init"}
  /\ EchoCount(p) >= N - 2 * T
  /\ EchoCount(p) <  N - T
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Echo"]
  /\ UNCHANGED << Correct, Faulty, recv >>

(* A correct process that has not yet accepted and now sees at least N-T
   distinct ECHO messages sends an ECHO (if it has not already) and
   accepts. *)
SendEchoAccept(p) ==
  /\ p \in Correct
  /\ pc[p] \in {"NoInit","Init","Echo"}
  /\ EchoCount(p) >= N - T
  /\ sent' = IF pc[p] # "Echo"
               THEN sent \cup { [type |-> "ECHO", sender |-> p] }
               ELSE sent
  /\ pc'   = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED << Correct, Faulty, recv >>

(* A correct process that has already sent ECHO and now sees at least N-T
   distinct ECHO messages accepts. *)
AcceptIfSent(p) ==
  /\ p \in Correct
  /\ pc[p] = "Echo"
  /\ EchoCount(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED << Correct, Faulty, recv, sent >>

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : SendEchoFromInit(p)
  \/ \E p \in Correct : SendEchoNoAccept(p)
  \/ \E p \in Correct : SendEchoAccept(p)
  \/ \E p \in Correct : AcceptIfSent(p)

(* --------------------------------------------------------------------- *)
(*   Specification                                                       *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(*   Invariants                                                          *)
(* --------------------------------------------------------------------- *)

TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \\ Correct
  /\ pc \in [Proc -> {"NoInit","Init","Echo","Accept"}]
  /\ recv \in [Proc -> SUBSET Message]
  /\ sent \subseteq Message
  /\ \A m \in sent : m.type = "ECHO" /\ m.sender \in Correct

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* --------------------------------------------------------------------- *)
(*   Liveness properties                                                 *)
(* --------------------------------------------------------------------- *)

CorrLtl  == [] (AllInit => <> AllAccept)
RelayLtl == [] (ExistsAccept => <> AllAccept)
UnforgLtl == [] (AllNoInit => [] ~ExistsAccept)

(* --------------------------------------------------------------------- *)
(*   Theorems (optional, for TLC)                                         *)
(* --------------------------------------------------------------------- *)

THEOREM Spec => []TypeOK
THEOREM Spec => FCConstraints

====