---- MODULE bcastByz ----
EXTENDS Naturals, TLC

CONSTANTS N, T, F

ASSUME N > 3 * T
ASSUME T >= F
ASSUME F >= 0

(* ----------------------------------------------------------------------
   Process set
   ---------------------------------------------------------------------- *)
Proc == 1..N

VARIABLES Correct, Faulty, pc, rec, sent

vars == <<Correct, Faulty, pc, rec, sent>>

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)
Init ==
  /\ Correct \in SUBSET Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ \E InitSet \in SUBSET Correct :
        /\ pc = [p \in Correct |-> IF p \in InitSet THEN "Accepted" ELSE "NoInit"]
        /\ sent = InitSet
        /\ rec = [p \in Proc |-> {}]

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
AvailableMsgs == sent \cup Faulty

(* ----------------------------------------------------------------------
   One step of a correct process p
   ---------------------------------------------------------------------- *)
ProcStep(p) ==
  /\ p \in Correct
  /\ \E new \in SUBSET AvailableMsgs :
        LET recNew == rec[p] \cup new IN
        /\ rec' = [rec EXCEPT ![p] = recNew]
        /\ CASE
               pc[p] = "NoInit" /\ Cardinality(recNew) >= N - T ->
                  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
                  /\ sent' = sent \cup {p}
           []  pc[p] = "NoInit" /\ Cardinality(recNew) >= N - 2 * T
                               /\ Cardinality(recNew) <  N - T ->
                  /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
                  /\ sent' = sent \cup {p}
           []  pc[p] = "EchoSent" /\ Cardinality(recNew) >= N - T ->
                  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
                  /\ sent' = sent
           []  OTHER ->
                  /\ pc'   = pc
                  /\ sent' = sent
        /\ UNCHANGED <<Correct, Faulty>>

Next ==
  \E p \in Correct : ProcStep(p)

Spec ==
  Init /\ [][Next]_vars /\ \A p \in Proc : WF_vars(ProcStep(p))

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ pc \in [Correct -> {"NoInit","EchoSent","Accepted"}]
  /\ sent \subseteq Correct
  /\ rec \in [Proc -> SUBSET Proc]

(* ----------------------------------------------------------------------
   Additional safety constraints
   ---------------------------------------------------------------------- *)
FCConstraints ==
  /\ \A p \in Correct : (pc[p] = "Accepted") => p \in sent
  /\ sent = {p \in Correct : pc[p] \in {"EchoSent","Accepted"}}

(* ----------------------------------------------------------------------
   LTL properties
   ---------------------------------------------------------------------- *)
CorrLtl ==
  [] ( ( \A p \in Correct : pc[p] = "Accepted")
        => <> ( \A p \in Correct : pc[p] = "Accepted") )

RelayLtl ==
  [] ( ( \E p \in Correct : pc[p] = "Accepted")
        => <> ( \A p \in Correct : pc[p] = "Accepted") )

UnforgLtl ==
  [] ( ( \A p \in Correct : pc[p] = "NoInit")
        => [] ( \A p \in Correct : pc[p] # "Accepted") )

====