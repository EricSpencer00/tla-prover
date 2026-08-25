---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process set and message definition
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, hasInit, echoSent, accepted, recv, sent

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ hasInit \in [Proc -> BOOLEAN]
  /\ \A p \in Proc \ Correct: hasInit[p] = FALSE
  /\ echoSent = [p \in Proc |-> FALSE]
  /\ accepted = [p \in Proc |-> FALSE]

\* ----------------------------------------------------------------------
\* Helper: distinct senders of ECHO messages received by a process
\* ----------------------------------------------------------------------
DistinctSenders(p, r) == { m.sender : m \in r[p] }

\* ----------------------------------------------------------------------
\* One combined receive‑and‑act step for a correct process p
\* ----------------------------------------------------------------------
ProcStep(p) ==
  /\ p \in Correct
  /\ \E newMsgs \in SUBSET Message :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
        /\ LET senders == DistinctSenders(p, recv') IN
           IF hasInit[p] /\ ~echoSent[p] /\ ~accepted[p] THEN
               /\ echoSent' = [echoSent EXCEPT ![p] = TRUE]
               /\ accepted' = [accepted EXCEPT ![p] = TRUE]
               /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
           ELSIF ~hasInit[p] /\ ~echoSent[p] /\ ~accepted[p] /\ Cardinality(senders) >= N - 2*T /\ Cardinality(senders) < N - T THEN
               /\ echoSent' = [echoSent EXCEPT ![p] = TRUE]
               /\ accepted' = accepted
               /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
           ELSIF ~hasInit[p] /\ ~echoSent[p] /\ ~accepted[p] /\ Cardinality(senders) >= N - T THEN
               /\ echoSent' = [echoSent EXCEPT ![p] = TRUE]
               /\ accepted' = [accepted EXCEPT ![p] = TRUE]
               /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
           ELSIF echoSent[p] /\ ~accepted[p] /\ Cardinality(senders) >= N - T THEN
               /\ accepted' = [accepted EXCEPT ![p] = TRUE]
               /\ echoSent' = echoSent
               /\ sent' = sent
           ELSE
               /\ echoSent' = echoSent
               /\ accepted' = accepted
               /\ sent' = sent
        /\ UNCHANGED <<Correct, Faulty, hasInit>>
        /\ UNCHANGED recv \ {p}
        /\ recv = recv'  \* make recv' the new value

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc : ProcStep(p)

\* ----------------------------------------------------------------------
\* Variable tuple for the temporal operators
\* ----------------------------------------------------------------------
vars == <<Correct, Faulty, hasInit, echoSent, accepted, recv, sent>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(ProcStep)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ sent \subseteq Message
  /\ \A m \in sent: m.type = "ECHO" /\ m.sender \in Correct
  /\ recv \in [Proc -> SUBSET Message]
  /\ \A p \in Proc: \A m \in recv[p] : m.type = "ECHO" /\ m.sender \in Proc
  /\ hasInit \in [Proc -> BOOLEAN]
  /\ echoSent \in [Proc -> BOOLEAN]
  /\ accepted \in [Proc -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Fault‑tolerance constraints
\* ----------------------------------------------------------------------
FCConstraints == N > 3 * T /\ T >= F

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
InitAllBroadcast == \A p \in Correct : hasInit[p]

CorrLtl == InitAllBroadcast => <> ( \A p \in Correct : accepted[p] )

RelayLtl == ( \E p \in Correct : accepted[p] ) => <> ( \A p \in Correct : accepted[p] )

UnforgLtl == ( \A p \in Correct : ~hasInit[p] ) => [] ( \A p \in Correct : ~accepted[p] )

====