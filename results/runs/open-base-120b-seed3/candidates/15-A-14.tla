---- MODULE bcastByz ----
EXTENDS FiniteSets, Naturals

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Basic sets and definitions
\* ----------------------------------------------------------------------
Proc == 1..N

Message == <<sender: Proc, type: {"ECHO"}>>

AllMsgs == { <<s, "ECHO">> : s \in Proc }

PCVals == {"NoInit", "InitRecv", "EchoSent", "Accepted", "Faulty"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

vars == <<Correct, Faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p) == { s \in Proc : <<s, "ECHO">> \in recv[p] }

CountEcho(p) == Cardinality(EchoSenders(p))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> PCVals]
  /\ \A p \in Correct :
        pc[p] \in {"NoInit", "InitRecv"}
  /\ \A p \in Faulty :
        pc[p] = "Faulty"
  /\ sent = {}
  /\ recv \in [Proc -> SUBSET AllMsgs]
  /\ \A p \in Proc : recv[p] = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ \E new \in SUBSET(AllMsgs) :
        /\ new \subseteq AllMsgs \ recv[p]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
  /\ UNCHANGED <<Correct, Faulty, pc, sent>>

EchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "InitRecv"
  /\ sent' = sent \cup { <<p, "ECHO">> }
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

EchoOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ CountEcho(p) >= N - 2 * T
  /\ CountEcho(p) <  N - T
  /\ sent' = sent \cup { <<p, "ECHO">> }
  /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

EchoAcceptNow(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ CountEcho(p) >= N - T
  /\ sent' = sent \cup { <<p, "ECHO">> }
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptLater(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ CountEcho(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, sent, recv>>

Next ==
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : EchoAndAccept(p)
  \/ \E p \in Proc : EchoOnly(p)
  \/ \E p \in Proc : EchoAcceptNow(p)
  \/ \E p \in Proc : AcceptLater(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> PCVals]
  /\ sent \subseteq AllMsgs
  /\ recv \in [Proc -> SUBSET AllMsgs]

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
  ( /\ \A p \in Correct : pc[p] = "InitRecv")
    => <> ( /\ \A p \in Correct : pc[p] = "Accepted")

RelayLtl ==
  [] ( ( \E p \in Correct : pc[p] = "Accepted")
        => <> ( /\ \A p \in Correct : pc[p] = "Accepted") )

UnforgLtl ==
  [] ( ( /\ \A p \in Correct : pc[p] = "NoInit")
        => ( /\ \A p \in Correct : pc[p] # "Accepted") )

====