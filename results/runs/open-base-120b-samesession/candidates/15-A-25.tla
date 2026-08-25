---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1 .. N

Msg == [type : {"ECHO"}, from : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, sent, recv, pc

vars == << Correct, Faulty, sent, recv, pc >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllMsgs == sent \cup { [type |-> "ECHO", from |-> f] : f \in Faulty }

RecvEchos(p) == { m.from : m \in recv[p] }

CountEchos(p) == Cardinality(RecvEchos(p))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ \E InitSet \subseteq Correct :
        pc = [p \in Proc |-> 
                IF p \in Correct 
                THEN IF p \in InitSet THEN "InitReceived" ELSE "Start0"
                ELSE "Start0"]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ \E new \subseteq (AllMsgs \ recv[p]) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED << sent, pc, Correct, Faulty >>

EchoSend(p) ==
  /\ p \in Correct
  /\ pc[p] # "Accepted"
  /\ LET cnt == CountEchos(p) IN
        /\ (pc[p] = "InitReceived"
            \/ (pc[p] = "Start0" /\ cnt >= N - 2*T))
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc' = [pc EXCEPT ![p] = 
            IF pc[p] = "InitReceived" \/ cnt >= N - T
            THEN "Accepted"
            ELSE "EchoSent0"]
  /\ UNCHANGED << recv, Correct, Faulty >>

Accept(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent0"
  /\ CountEchos(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED << sent, recv, Correct, Faulty >>

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : EchoSend(p)
  \/ \E p \in Correct : Accept(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Fairness (weak fairness on all steps of correct processes)
\* ----------------------------------------------------------------------
\* The model checker may include or omit this for safety checks.
\* Uncomment the line below to enable fairness.
\* WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ sent \subseteq Msg
  /\ recv \in [Proc -> SUBSET Msg]
  /\ pc \in [Proc -> {"Start0", "InitReceived", "EchoSent0", "Accepted"}]

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* Helper predicates for properties
\* ----------------------------------------------------------------------
AllAccepted == \A p \in Correct : pc[p] = "Accepted"
AnyAccepted == \E p \in Correct : pc[p] = "Accepted"
AllInitReceived == \A p \in Correct : pc[p] = "InitReceived"
AllStart0 == \A p \in Correct : pc[p] = "Start0"

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == (AllInitReceived) => <> AllAccepted

RelayLtl == (AnyAccepted) => <> AllAccepted

UnforgLtl == (AllStart0) => [] ( \A p \in Correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* Theorems (optional, useful for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====