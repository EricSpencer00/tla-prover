---- MODULE bcallByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F

\* ------------------------------------------------------------
\* Types
\* ------------------------------------------------------------
Proc == 1..N
Msg  == [type : {"ECHO"}, from : Proc]

\* ------------------------------------------------------------
\* Variables
\* ------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, sent

vars == <<Correct, Faulty, pc, recv, sent>>

\* ------------------------------------------------------------
\* Initial state
\* ------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ \E initSet \subseteq Correct :
        pc = [p \in Proc |-> 
                IF p \in initSet THEN "Init"
                ELSE IF p \in Correct THEN "NoInit"
                ELSE "Faulty"
             ]

\* ------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------
AllSent == sent \cup { [type |-> "ECHO", from |-> f] : f \in Faulty }

EchoMsg(p) == [type |-> "ECHO", from |-> p]

EchoSenders(rec) ==
  { m.from : m \in rec /\ m.type = "ECHO" }

NumEchoSenders(rec) ==
  Cardinality( EchoSenders(rec) )

\* ------------------------------------------------------------
\* One step of a correct process (receive arbitrary messages and act)
\* ------------------------------------------------------------
ProcessStep(p) ==
  /\ p \in Correct
  /\ LET newMsgs == SUBSET(AllSent) IN
     LET rec2   == recv[p] \cup newMsgs IN
     LET cnt    == NumEchoSenders(rec2) IN
     /\ recv' = [recv EXCEPT ![p] = rec2]
     /\ pc'   = [pc EXCEPT ![p] =
           IF pc[p] = "Init" THEN
                "Accepted"
           ELSE IF pc[p] = "NoInit" THEN
                IF cnt >= N - T THEN
                     "Accepted"
                ELSE IF cnt >= N - 2*T THEN
                     "EchoSent"
                ELSE "NoInit"
                END
           ELSE IF pc[p] = "EchoSent" THEN
                IF cnt >= N - T THEN "Accepted" ELSE "EchoSent"
           ELSE "Faulty"
         ]
     /\ sent' = IF pc[p] = "Init"
                \/ (pc[p] = "NoInit" /\ cnt >= N - 2*T)
                \/ (pc[p] = "NoInit" /\ cnt >= N - T)
                \/ (pc[p] = "EchoSent" /\ cnt >= N - T)
                THEN sent \cup { EchoMsg(p) }
                ELSE sent
     /\ UNCHANGED <<Correct, Faulty>>

Next ==
  \/ \E p \in Correct : ProcessStep(p)

\* ------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ------------------------------------------------------------
\* Invariants
\* ------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"Init","NoInit","EchoSent","Accepted","Faulty"}]
  /\ recv \in [Proc -> SUBSET Msg]
  /\ sent \subseteq Msg

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(Correct) = N - F

\* ------------------------------------------------------------
\* Auxiliary predicates for LTL properties
\* ------------------------------------------------------------
AllCorrectInit ==
  \A p \in Correct : pc[p] = "Init"

AllCorrectAccepted ==
  \A p \in Correct : pc[p] = "Accepted"

NoBroadcast ==
  \A p \in Correct : pc[p] = "NoInit"

NoAccept ==
  \A p \in Correct : pc[p] # "Accepted"

\* ------------------------------------------------------------
\* LTL properties
\* ------------------------------------------------------------
CorrLtl   == [] ( AllCorrectInit => <> AllCorrectAccepted )
RelayLtl  == [] ( (\E p \in Correct : pc[p] = "Accepted") => <> AllCorrectAccepted )
UnforgLtl == [] ( NoBroadcast => [] NoAccept )

====