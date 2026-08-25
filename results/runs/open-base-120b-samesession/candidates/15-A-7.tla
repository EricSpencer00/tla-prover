---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* ------------------------------------------------------------------------ *)
(*   Sets and Types                                                          *)
(* ------------------------------------------------------------------------ *)

Proc == 1..N

Message == [sender : Proc, type : {"ECHO"}]

(* ------------------------------------------------------------------------ *)
(*   Variables                                                               *)
(* ------------------------------------------------------------------------ *)

VARIABLES Correct, Faulty, pc, sent, recv

vars == <<Correct, Faulty, pc, sent, recv>>

(* ------------------------------------------------------------------------ *)
(*   Helper definitions                                                      *)
(* ------------------------------------------------------------------------ *)

EchoSenders(s) == { m.sender : m \in s /\ m.type = "ECHO" }

(* ------------------------------------------------------------------------ *)
(*   Initial state                                                          *)
(* ------------------------------------------------------------------------ *)

Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"StartNoInit", "StartInit", "EchoSent", "Accepted"}]
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ \A p \in Proc : pc[p] \in {"StartNoInit", "StartInit"}

(* ------------------------------------------------------------------------ *)
(*   Action for a correct process p                                          *)
(* ------------------------------------------------------------------------ *)

Action(p) ==
  /\ p \in Correct
  /\ LET
        allPossibleMsgs == sent \cup { [sender |-> f, type |-> "ECHO"] : f \in Faulty }
        newMsgs          == SUBSET (allPossibleMsgs \ recv[p])
        recvPrime        == [recv EXCEPT ![p] = @ \cup newMsgs]
        echoCnt          == Cardinality( EchoSenders(recvPrime[p]) )
        pcNow            == pc[p]
     IN
        /\ CASE
            pcNow = "StartInit" ->
               /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
               /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
               /\ recv' = recvPrime
            pcNow = "StartNoInit" /\ echoCnt >= N - T ->
               /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
               /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
               /\ recv' = recvPrime
            pcNow = "StartNoInit" /\ echoCnt >= N - 2*T /\ echoCnt < N - T ->
               /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
               /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
               /\ recv' = recvPrime
            pcNow = "EchoSent" /\ echoCnt >= N - T ->
               /\ sent' = sent
               /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
               /\ recv' = recvPrime
            OTHER ->
               /\ sent' = sent
               /\ pc'   = pc
               /\ recv' = recvPrime
        END CASE
  /\ UNCHANGED <<Correct, Faulty>>

(* ------------------------------------------------------------------------ *)
(*   Next-step relation                                                     *)
(* ------------------------------------------------------------------------ *)

Next ==
  \/ \E p \in Correct : Action(p)

(* ------------------------------------------------------------------------ *)
(*   Specification                                                          *)
(* ------------------------------------------------------------------------ *)

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

(* ------------------------------------------------------------------------ *)
(*   Invariants                                                             *)
(* ------------------------------------------------------------------------ *)

TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"StartNoInit", "StartInit", "EchoSent", "Accepted"}]
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]
  /\ \A m \in sent : m.sender \in Correct
  /\ \A p \in Proc : \A m \in recv[p] : m.sender \in Proc

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* ------------------------------------------------------------------------ *)
(*   LTL properties                                                          *)
(* ------------------------------------------------------------------------ *)

AllCorrectInit == \A p \in Correct : pc[p] = "StartInit"
AllCorrectAccepted == \A p \in Correct : pc[p] = "Accepted"
AnyCorrectAccepted == \E p \in Correct : pc[p] = "Accepted"
NoInitAtStart == \A p \in Correct : pc[p] = "StartNoInit"

CorrLtl   == [] ( AllCorrectInit => <> AllCorrectAccepted )
RelayLtl  == [] ( AnyCorrectAccepted => <> AllCorrectAccepted )
UnforgLtl == [] ( NoInitAtStart => [] ( \A p \in Correct : pc[p] # "Accepted") )

====