---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

(* ------------------------------------------------------------------- *)
(* Process set *)
Proc == 1..N

(* ------------------------------------------------------------------- *)
(* Message definition (only ECHO messages) *)
ECHO == "ECHO"
Msg == <<Proc, ECHO>>  \* just a notation; actual messages are pairs <<p, ECHO>>

(* ------------------------------------------------------------------- *)
(* Variables *)
VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

(* ------------------------------------------------------------------- *)
(* Helper definitions *)

ByzMsgs == { <<f, ECHO>> : f \in faulty }

ReceivedEchoes(p, r) == { s \in Proc : <<s, ECHO>> \in r }

EchoCount(p, r) == Cardinality( ReceivedEchoes(p, r) )

EchoMsg(p) == <<p, ECHO>>

(* ------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ correct \subseteq Proc
  /\ Cardinality(correct) = N - F
  /\ faulty = Proc \ correct
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ pc \in [Proc -> {"NoInit", "InitRecv"}]   \* each process either has or has not received INIT

(* ------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
  \E p \in correct :
    LET newMsgs == SUBSET( (sent \cup ByzMsgs) \ recv[p] ) IN
    LET r' == recv[p] \cup newMsgs IN
    LET cnt == EchoCount(p, r') IN
    /\ recv' = [recv EXCEPT ![p] = r']
    /\ pc' = [pc EXCEPT ![p] =
          IF pc[p] = "Accepted" THEN "Accepted"
          ELSE IF pc[p] = "InitRecv" THEN "Accepted"
          ELSE IF pc[p] = "NoInit"  /\ cnt >= N - 2*T /\ cnt < N - T THEN "EchoSent"
          ELSE IF pc[p] = "NoInit"  /\ cnt >= N - T THEN "Accepted"
          ELSE IF pc[p] = "EchoSent" /\ cnt >= N - T THEN "Accepted"
          ELSE pc[p] ]
    /\ sent' = IF
                 (pc[p] = "InitRecv") \/
                 (pc[p] = "NoInit"  /\ cnt >= N - 2*T) \/
                 (pc[p] = "NoInit"  /\ cnt >= N - T) \/
                 (pc[p] = "EchoSent")   \* already sent, keep idempotent
               THEN sent \cup { EchoMsg(p) }
               ELSE sent
    /\ UNCHANGED <<correct, faulty>>

(* ------------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ------------------------------------------------------------------- *)
(* Type invariants *)

TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty = Proc \ correct
  /\ pc \in [Proc -> {"NoInit","InitRecv","EchoSent","Accepted"}]
  /\ recv \in [Proc -> SUBSET (Proc \X {"ECHO"})]
  /\ sent \in SUBSET (Proc \X {"ECHO"})
  /\ \A p \in Proc : (<<p, ECHO>> \in sent) => p \in correct

(* ------------------------------------------------------------------- *)
(* Faulty‑process constraints *)

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F

(* ------------------------------------------------------------------- *)
(* LTL properties *)

AllInit == \A p \in correct : pc[p] = "InitRecv"
AllNoInit == \A p \in correct : pc[p] = "NoInit"
AllAccepted == \A p \in correct : pc[p] = "Accepted"
NoAccepted == \A p \in correct : pc[p] # "Accepted"

CorrLtl == (Init /\ AllInit) => <> AllAccepted

RelayLtl == [] ( (\E p \in correct : pc[p] = "Accepted") => <> AllAccepted )

UnforgLtl == [] ( AllNoInit => [] NoAccepted )

====