---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
AllEchos == { [sender |-> s, type |-> "ECHO"] : s \in 1..N }

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchosFrom(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }

CountEchos(p) == Cardinality(EchosFrom(p))

NMinus2T == N - 2 * T
NMinusT  == N - T

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ \E FaultySet \in SUBSET 1..N :
        /\ Cardinality(FaultySet) = F
        /\ Faulty = FaultySet
        /\ Correct = 1..N \ FaultySet
  /\ \E InitSet \in SUBSET Correct :
        /\ sent = { [sender |-> p, type |-> "ECHO"] : p \in InitSet }
        /\ pc = [p \in 1..N |-> 
                IF p \in Faulty THEN "Faulty"
                ELSE IF p \in InitSet THEN "Accepted"
                ELSE "NoInit"]
        /\ recv = [p \in 1..N |-> 
                IF p \in InitSet THEN { [sender |-> p, type |-> "ECHO"] }
                ELSE {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ pc[p] \in {"NoInit", "EchoSent"}
  /\ LET possible == (sent \cup AllEchos) \ recv[p] IN
        /\ newMsgs \subseteq possible
  /\ UNCHANGED <<Correct, Faulty, pc, sent>>
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]

SendEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ CountEchos(p) >= NMinus2T
  /\ CountEchos(p) < NMinusT
  /\ LET m == [sender |-> p, type |-> "ECHO"] IN
        /\ sent' = sent \cup {m}
        /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED <<Correct, Faulty>>

SendAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ CountEchos(p) >= NMinusT
  /\ LET m == [sender |-> p, type |-> "ECHO"] IN
        /\ sent' = sent \cup {m}
        /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED <<Correct, Faulty>>

AcceptAfterSend(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ CountEchos(p) >= NMinusT
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, sent, recv>>

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : SendEcho(p)
  \/ \E p \in Correct : SendAndAccept(p)
  \/ \E p \in Correct : AcceptAfterSend(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Correct, Faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq 1..N
  /\ Faulty = 1..N \ Correct
  /\ pc \in [1..N -> {"NoInit", "EchoSent", "Accepted", "Faulty"}]
  /\ sent \subseteq AllEchos
  /\ recv \in [1..N -> SUBSET AllEchos]

FCConstraints ==
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ N > 3 * T
  /\ T >= F

\* ----------------------------------------------------------------------
\* LTL Properties
\* ----------------------------------------------------------------------
AllCorrectAccepted == \A p \in Correct : pc[p] = "Accepted"
SomeCorrectAccepted == \E p \in Correct : pc[p] = "Accepted"

CorrLtl == [] ( AllCorrectAccepted => <> AllCorrectAccepted )
RelayLtl == [] ( SomeCorrectAccepted => <> AllCorrectAccepted )
UnforgLtl == ( \A p \in Correct : pc[p] # "Accepted" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====