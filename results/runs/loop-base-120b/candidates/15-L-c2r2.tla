---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Sets and derived constants
\* ----------------------------------------------------------------------
Proc == 1 .. N

ECHO == "ECHO"

Message == [sender : Proc, type : {ECHO}]

SentECHO(p) == [sender |-> p, type |-> ECHO]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, sent

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"Init", "NoInit", "EchoSent", "Accepted", "Faulty"}]
  /\ recv \in [Proc -> SUBSET Message]
  /\ sent \subseteq { SentECHO(p) : p \in Correct }

\* ----------------------------------------------------------------------
\* Fault‑containment constraints (invariants)
\* ----------------------------------------------------------------------
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ Correct \cup Faulty = Proc
  /\ Correct \cap Faulty = {}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ \E InitSet \in SUBSET Correct :
        /\ pc = [p \in Proc |
                   IF p \in Correct
                   THEN IF p \in InitSet THEN "Init" ELSE "NoInit"
                   ELSE "Faulty"]
        /\ recv = [p \in Proc |-> {}]
        /\ sent = {}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ByzMsgSet == { [sender |-> f, type |-> ECHO] : f \in Faulty }

Nminus2T == N - 2 * T
NminusT  == N - T

DistinctSenders(mset) == { m.sender : m \in mset, m.type = ECHO }

\* ----------------------------------------------------------------------
\* Action of a correct process (receive new messages and possibly act)
\* ----------------------------------------------------------------------
ProcAction(p) ==
  /\ p \in Correct
  /\ \E newMsgs \in SUBSET ((sent \cup ByzMsgSet) \ recv[p]) :
        LET newRecv == recv[p] \cup newMsgs
            sndrs   == DistinctSenders(newRecv)
            condInit == pc[p] = "Init"
            condNoInitSend == pc[p] = "NoInit" /\ Cardinality(sndrs) >= Nminus2T
            condEchoSentAccept == pc[p] = "EchoSent" /\ Cardinality(sndrs) >= NminusT
            sendNow   == condInit \/ condNoInitSend
            acceptNow == condInit
                         \/ (pc[p] = "NoInit" /\ Cardinality(sndrs) >= NminusT)
                         \/ condEchoSentAccept
            newPc   == IF acceptNow THEN "Accepted"
                       ELSE IF sendNow THEN "EchoSent"
                       ELSE pc[p]
            newSent == IF sendNow THEN sent \cup { SentECHO(p) } ELSE sent
        IN
           /\ pc'   = [pc EXCEPT ![p] = newPc]
           /\ recv' = [recv EXCEPT ![p] = newRecv]
           /\ sent' = newSent

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Correct : ProcAction(p)

vars == <<Correct, Faulty, pc, recv, sent>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* LTL‑style properties
\* ----------------------------------------------------------------------
AllAccepted == \A p \in Correct : pc[p] = "Accepted"

InitAllInit == \A p \in Correct : pc[p] = "Init"

NoInitAll == \A p \in Correct : pc[p] = "NoInit"

SomeAccepted == \E p \in Correct : pc[p] = "Accepted"

CorrLtl == [] (InitAllInit => <> AllAccepted)

RelayLtl == [] (SomeAccepted => <> AllAccepted)

UnforgLtl == [] (NoInitAll => [] (~SomeAccepted))

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
\* (already defined with the exact names above)

====