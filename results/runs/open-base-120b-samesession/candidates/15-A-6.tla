---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* --------------------------------------------------------------------------- *)
(* Basic sets *)

Proc == 1 .. N

Message == [sender : Proc, type : {"ECHO"}]

ECHOmsg(s) == [sender |-> s, type |-> "ECHO"]

PossibleMsgs == { ECHOmsg(p) : p \in Proc }

(* --------------------------------------------------------------------------- *)
(* State variables *)

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

(* --------------------------------------------------------------------------- *)
(* Helper definitions *)

ReceivedEchoes(p) == { m.sender : m \in recv[p] }

CntEcho(p) == Cardinality(ReceivedEchoes(p))

NMinus2T == N - 2 * T
NMinusT  == N - T

(* --------------------------------------------------------------------------- *)
(* Initial state *)

Init ==
/\ correct \subseteq Proc
/\ faulty = Proc \ correct
/\ Cardinality(correct) = N - F
/\ \A p \in Proc : pc[p] \in {"Start0", "Start1"}   \* Start0 = no INIT, Start1 = INIT received
/\ sent = {}
/\ recv = [p \in Proc |-> {}]

(* --------------------------------------------------------------------------- *)
(* Actions *)

ReceiveAction ==
\E p \in correct :
  \E new \subseteq (PossibleMsgs \ recv[p]) :
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

InitAccept ==
\E p \in correct :
  /\ pc[p] = "Start1"
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ sent' = sent \cup { ECHOmsg(p) }
  /\ UNCHANGED <<correct, faulty, recv>>

EchoNoAccept ==
\E p \in correct :
  /\ pc[p] = "Start0"
  /\ CntEcho(p) >= NMinus2T
  /\ CntEcho(p) <  NMinusT
  /\ pc' = [pc EXCEPT ![p] = "Echo"]
  /\ sent' = sent \cup { ECHOmsg(p) }
  /\ UNCHANGED <<correct, faulty, recv>>

EchoAndAccept ==
\E p \in correct :
  /\ pc[p] = "Start0"
  /\ CntEcho(p) >= NMinusT
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ sent' = sent \cup { ECHOmsg(p) }
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptOnly ==
\E p \in correct :
  /\ pc[p] = "Echo"
  /\ CntEcho(p) >= NMinusT
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
\/ ReceiveAction
\/ InitAccept
\/ EchoNoAccept
\/ EchoAndAccept
\/ AcceptOnly

(* --------------------------------------------------------------------------- *)
(* Specification *)

Spec ==
Init /\ [][Next]_vars /\ WF_vars(ReceiveAction)

(* --------------------------------------------------------------------------- *)
(* Type invariants *)

TypeOK ==
/\ correct \subseteq Proc
/\ faulty = Proc \ correct
/\ pc \in [Proc -> {"Start0","Start1","Echo","Accept"}]
/\ recv \in [Proc -> SUBSET PossibleMsgs]
/\ sent \subseteq PossibleMsgs

FCConstraints ==
/\ N > 3 * T
/\ T >= F
/\ F >= 0

(* --------------------------------------------------------------------------- *)
(* LTL properties *)

CorrLtl ==
[] ( ( \A p \in correct : pc[p] = "Start1")
      => <> ( \A p \in correct : pc[p] = "Accept") )

RelayLtl ==
[] ( ( \E p \in correct : pc[p] = "Accept")
      => <> ( \A p \in correct : pc[p] = "Accept") )

UnforgLtl ==
[] ( ( \A p \in correct : pc[p] = "Start0")
      => [] ( \A p \in correct : pc[p] # "Accept") )

=============================================================================