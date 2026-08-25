---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* ------------------------------------------------------------------- *)
(* Process set *)
Proc == 1..N

(* ------------------------------------------------------------------- *)
(* Variables *)
VARIABLES Correct, Faulty, pc, recv, sent, initSet

(* ------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ initSet \subseteq Correct
  /\ pc \in [Proc -> {"NoInit","InitRecvd","Echoed","Accepted"}]
  /\ recv \in [Proc -> SUBSET Proc]
  /\ sent \subseteq Correct

(* ------------------------------------------------------------------- *)
(* Fault‑count constraints *)
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ initSet \subseteq Correct
  /\ pc = [p \in Proc |-> IF p \in initSet THEN "InitRecvd" ELSE "NoInit"]
  /\ recv = [p \in Proc |-> {}]
  /\ sent = {}

(* ------------------------------------------------------------------- *)
(* Helper definitions *)
RecvSet(p) == recv[p]
RecvCount(p) == Cardinality(RecvSet(p))

PossibleSenders(p) == (sent \cup Faulty) \ RecvSet(p)

(* ------------------------------------------------------------------- *)
(* One atomic step of a correct process: receive any new messages
   (including Byzantine ones) and possibly send ECHO / accept *)
ProcStep(p) ==
  /\ p \in Correct
  /\ \E new \in SUBSET PossibleSenders(p) :
        /\ recv' = [recv EXCEPT ![p] = RecvSet(p) \cup new]
        /\ LET rnew == RecvSet(p) \cup new IN
               rcnt == Cardinality(rnew) IN
           CASE
             pc[p] = "InitRecvd" ->
               /\ sent' = sent \cup {p}
               /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
           [] pc[p] = "NoInit" /\ rcnt >= N - T ->
               /\ sent' = sent \cup {p}
               /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
           [] pc[p] = "NoInit" /\ rcnt >= N - 2*T /\ rcnt < N - T ->
               /\ sent' = sent \cup {p}
               /\ pc'   = [pc EXCEPT ![p] = "Echoed"]
           [] pc[p] = "Echoed" /\ rcnt >= N - T ->
               /\ sent' = sent
               /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
           [] OTHER ->
               /\ sent' = sent
               /\ pc'   = pc
  /\ UNCHANGED <<Correct, Faulty, initSet>>

(* ------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
  \E p \in Correct : ProcStep(p)

vars == <<Correct, Faulty, pc, recv, sent, initSet>>

(* ------------------------------------------------------------------- *)
(* Specification with weak fairness on ProcStep for each correct process *)
Spec ==
  Init /\ [][Next]_vars /\ \A p \in Correct : WF_vars(ProcStep(p))

(* ------------------------------------------------------------------- *)
(* LTL properties *)

InitAll == initSet = Correct
AllAccepted == \A p \in Correct : pc[p] = "Accepted"
ExistsAccepted == \E p \in Correct : pc[p] = "Accepted"
NoInit == initSet = {}

CorrLtl == [] (InitAll => <> AllAccepted)
RelayLtl == [] (ExistsAccepted => <> AllAccepted)
UnforgLtl == [] (NoInit => [] (\A p \in Correct : pc[p] # "Accepted"))

====