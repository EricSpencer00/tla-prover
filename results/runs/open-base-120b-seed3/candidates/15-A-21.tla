---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES Correct, Faulty, pc, recv, sent

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

AllMsgs == { [type |-> "ECHO", sender |-> p] : p \in 1..N }

EchoMsg(p) == [type |-> "ECHO", sender |-> p]

EchoSenders(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }

Cnt(p) == Cardinality(EchoSenders(p))

NMinus2T == N - 2 * T
NMinusT  == N - T

vars == <<Correct, Faulty, pc, recv, sent>>

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ Correct \subseteq 1..N
  /\ Cardinality(Correct) = N - F
  /\ Faulty = (1..N) \ Correct
  /\ pc \in [1..N -> {"NoInit", "Init", "EchoSent", "Accepted"}]
  /\ \A p \in Correct : pc[p] \in {"NoInit", "Init"}
  /\ recv \in [1..N -> SUBSET AllMsgs]
  /\ sent = {}

(* ---------------------------------------------------------------------- *)
(* Actions *)

Receive(p) ==
  /\ p \in Correct
  /\ \E newMsgs \in SUBSET AllMsgs :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

InitAcceptSend(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ Cnt(p) >= NMinusT
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ Cnt(p) >= NMinus2T
  /\ Cnt(p) < NMinusT
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ Cnt(p) >= NMinusT
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv, sent>>

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : InitAcceptSend(p)
  \/ \E p \in Correct : SendEchoAndAccept(p)
  \/ \E p \in Correct : SendEchoOnly(p)
  \/ \E p \in Correct : AcceptOnly(p)

(* ---------------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
  /\ Correct \subseteq 1..N
  /\ Cardinality(Correct) = N - F
  /\ Faulty = (1..N) \ Correct
  /\ pc \in [1..N -> {"NoInit", "Init", "EchoSent", "Accepted"}]
  /\ \A p \in Correct : pc[p] \in {"NoInit", "Init", "EchoSent", "Accepted"}
  /\ recv \in [1..N -> SUBSET AllMsgs]
  /\ sent \subseteq AllMsgs
  /\ \A m \in sent : m.type = "ECHO" /\ m.sender \in Correct

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(* ---------------------------------------------------------------------- *)
(* LTL properties *)

CorrLtl ==
  [] ( ( \A p \in Correct : pc[p] = "Init")
        => <> ( \A p \in Correct : pc[p] = "Accepted") )

RelayLtl ==
  [] ( ( \E p \in Correct : pc[p] = "Accepted")
        => <> ( \A p \in Correct : pc[p] = "Accepted") )

UnforgLtl ==
  ( \A p \in Correct : pc[p] = "NoInit")
    => [] ( \A p \in Correct : pc[p] # "Accepted")

====