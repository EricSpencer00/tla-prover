---- MODULE bcastByz ----
EXTENDS FiniteSets, Naturals, TLC

CONSTANTS N, T, F

(* ------------------------------------------------------------------- *)
(* Process set *)
Proc == 1..N

(* Message definition (only ECHO messages) *)
Msg == [sender : Proc, typ : {"ECHO"}]

(* ------------------------------------------------------------------- *)
VARIABLES Correct, Faulty, pc, sent, rec

(* ------------------------------------------------------------------- *)
(* Helper definitions *)
NMinus2T == N - 2 * T
NMinusT  == N - T

ByzMsgs == SUBSET { [sender |-> f, typ |-> "ECHO"] : f \in Faulty }

EchoSenders(p, r) == { m.sender : m \in r[p] /\ m.typ = "ECHO" }

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  LET initRecv == SUBSET Correct IN
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \\ Correct
    /\ sent = { [sender |-> p, typ |-> "ECHO"] : p \in initRecv }
    /\ rec = [p \in Proc |-> {}]
    /\ pc = [p \in Proc |-> IF p \in initRecv THEN "Accepted" ELSE "NoEcho"]

(* ------------------------------------------------------------------- *)
(* One combined receive‑and‑act step for a correct process p *)
ReceiveAct(p) ==
  LET newMsgs == SUBSET ( sent \cup ByzMsgs ) \\ rec[p] IN
    /\ rec' = [rec EXCEPT ![p] = rec[p] \cup newMsgs]
    /\ CASE
         pc[p] = "NoEcho" ->
           IF Cardinality( EchoSenders(p, rec') ) >= NMinusT THEN
               /\ pc' = [pc EXCEPT ![p] = "Accepted"]
               /\ sent' = sent \cup { [sender |-> p, typ |-> "ECHO"] }
           ELSE IF Cardinality( EchoSenders(p, rec') ) >= NMinus2T THEN
               /\ pc' = [pc EXCEPT ![p] = "Echoed"]
               /\ sent' = sent \cup { [sender |-> p, typ |-> "ECHO"] }
           ELSE
               /\ pc' = pc
               /\ sent' = sent
         pc[p] = "Echoed" ->
           IF Cardinality( EchoSenders(p, rec') ) >= NMinusT THEN
               /\ pc' = [pc EXCEPT ![p] = "Accepted"]
               /\ UNCHANGED sent
           ELSE
               /\ pc' = pc
               /\ UNCHANGED sent
         pc[p] = "Accepted" ->
           /\ UNCHANGED <<pc, sent>>
         OTHER -> UNCHANGED <<pc, sent>>
       END CASE
    /\ UNCHANGED <<Correct, Faulty>>

(* ------------------------------------------------------------------- *)
Next ==
  \E p \in Correct : ReceiveAct(p)

vars == <<Correct, Faulty, pc, sent, rec>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \\ Correct
  /\ pc \in [Proc -> {"NoEcho", "Echoed", "Accepted"}]
  /\ sent \subseteq { [sender |-> p, typ |-> "ECHO"] : p \in Correct }
  /\ rec \in [Proc -> SUBSET { [sender |-> p, typ |-> "ECHO"] : p \in Proc }]

(* ------------------------------------------------------------------- *)
(* Fault‑containment constraints invariant *)
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F

(* ------------------------------------------------------------------- *)
(* LTL properties *)

CorrLtl ==
  [] ( ( \A p \in Correct : pc[p] = "Accepted")
        => <> ( \A p \in Correct : pc[p] = "Accepted") )

RelayLtl ==
  [] ( ( \E p \in Correct : pc[p] = "Accepted")
        => <> ( \A p \in Correct : pc[p] = "Accepted") )

UnforgLtl ==
  [] ( ( \A p \in Correct : pc[p] = "NoEcho")
        => [] ( \A p \in Correct : pc[p] # "Accepted") )

====