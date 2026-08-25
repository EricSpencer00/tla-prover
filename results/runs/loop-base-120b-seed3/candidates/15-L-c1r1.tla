---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, T, F

\* ----------------------------------------------------------------------
\* Process set and message definition
\* ----------------------------------------------------------------------
Proc == 1 .. N

Message == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, initSet, echoSent, accepted, recv, sent

Vars == <<Correct, Faulty, initSet, echoSent, accepted, recv, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ByzMsgs == { [type |-> "ECHO", sender |-> f] : f \in Faulty }

EchoMsg(p) == [type |-> "ECHO", sender |-> p]

cnt(p) == Cardinality({ m.sender : m \in recv[p] /\ m.type = "ECHO" })

\* ----------------------------------------------------------------------
\* Fairness definitions (replicating Temporal module)
\* ----------------------------------------------------------------------
Enabled(A) ==
  \E <<Correct', Faulty', initSet', echoSent', accepted', recv', sent'>> : A

WF_Vars(A) == []<>(~Enabled(A) \/ <> (A))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ initSet \subseteq Correct
  /\ echoSent = initSet
  /\ accepted = initSet
  /\ sent = { EchoMsg(p) : p \in initSet }
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions for a single correct process p
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ LET possible == (sent \cup ByzMsgs) \ recv[p] IN
       \E new \in SUBSET possible :
         /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
         /\ UNCHANGED <<Correct, Faulty, initSet, echoSent, accepted, sent>>

SendEcho(p) ==
  /\ p \in Correct
  /\ p \notin echoSent
  /\ cnt(p) >= N - 2 * T
  /\ cnt(p) < N - T
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ echoSent' = echoSent \cup {p}
  /\ UNCHANGED <<Correct, Faulty, initSet, accepted, recv>>

SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ p \notin echoSent
  /\ cnt(p) >= N - T
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ echoSent' = echoSent \cup {p}
  /\ accepted' = accepted \cup {p}
  /\ UNCHANGED <<Correct, Faulty, initSet, recv>>

Accept(p) ==
  /\ p \in Correct
  /\ p \in echoSent
  /\ p \notin accepted
  /\ cnt(p) >= N - T
  /\ accepted' = accepted \cup {p}
  /\ UNCHANGED <<Correct, Faulty, initSet, echoSent, recv, sent>>

ProcStep(p) ==
  \/ Receive(p)
  \/ SendEcho(p)
  \/ SendEchoAndAccept(p)
  \/ Accept(p)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \E p \in Proc : ProcStep(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_Vars /\ \A p \in Proc : (p \in Correct => WF_Vars(ProcStep(p)))

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ initSet \subseteq Correct
  /\ echoSent \subseteq Correct
  /\ accepted \subseteq Correct
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]
  /\ \A p \in Proc : \A m \in recv[p] : m \in Message
  /\ \A m \in sent : m.type = "ECHO" /\ m.sender \in Correct

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ Correct \cap Faulty = {}
  /\ Correct \cup Faulty = Proc

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == (initSet = Correct) => <> (accepted = Correct)

RelayLtl == [] ( ( \E p \in Correct : p \in accepted ) => <> (accepted = Correct) )

UnforgLtl == (initSet = {}) => [] (accepted \cap Correct = {})

====