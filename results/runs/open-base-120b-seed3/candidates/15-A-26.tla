---- MODULE bcastByz ----
EXTENDS FiniteSets, Naturals, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N

Kind == {"ECHO"}

Msg == [sender : Proc, kind : Kind]

ProcState == {"NoInit", "InitReceived", "EchoSent", "Accepted"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, rec, init

vars == <<Correct, Faulty, pc, sent, rec, init>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoMsg(p) == [sender |-> p, kind |-> "ECHO"]

EchoSenders(p) == { m.sender : m \in rec[p] /\ m.kind = "ECHO" }

CntEcho(p) == Cardinality(EchoSenders(p))

AllPossibleMsgs == sent \cup { EchoMsg(f) : f \in Faulty }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ init \subseteq Correct
    /\ pc = [p \in Proc |-> IF p \in init THEN "InitReceived" ELSE "NoInit"]
    /\ sent = {}
    /\ rec = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in Correct
    /\ LET newMsgs == SUBSET AllPossibleMsgs IN
       /\ newMsgs \subseteq AllPossibleMsgs
    /\ rec' = [rec EXCEPT ![p] = rec[p] \cup newMsgs]
    /\ UNCHANGED <<Correct, Faulty, pc, sent, init>>

SendEcho(p) ==
    /\ p \in Correct
    /\ sent' = sent \cup { EchoMsg(p) }
    /\ UNCHANGED <<Correct, Faulty, pc, rec, init>>

Act(p) ==
    \/ /\ pc[p] = "InitReceived"
       /\ pc' = [pc EXCEPT ![p] = "Accepted"]
       /\ SendEcho(p)
    \/ /\ pc[p] = "NoInit"
       /\ CntEcho(p) >= N - 2*T
       /\ CntEcho(p) < N - T
       /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
       /\ SendEcho(p)
    \/ /\ pc[p] = "NoInit"
       /\ CntEcho(p) >= N - T
       /\ pc' = [pc EXCEPT ![p] = "Accepted"]
       /\ SendEcho(p)
    \/ /\ pc[p] = "EchoSent"
       /\ CntEcho(p) >= N - T
       /\ pc' = [pc EXCEPT ![p] = "Accepted"]
       /\ UNCHANGED sent

Next ==
    \E p \in Correct : Receive(p) \/ Act(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(\E p \in Correct : Act(p))   \* weak fairness on the action steps

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ init \subseteq Correct
    /\ pc \in [Proc -> ProcState]
    /\ sent \subseteq Msg
    /\ rec \in [Proc -> SUBSET Msg]

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* Temporal properties
\* ----------------------------------------------------------------------
CorrLtl ==
    [] (init = Correct => <> (\A p \in Correct : pc[p] = "Accepted"))

RelayLtl ==
    [] ( (\E p \in Correct : pc[p] = "Accepted") => <> (\A q \in Correct : pc[q] = "Accepted") )

UnforgLtl ==
    [] (init = {} => [] (\A p \in Correct : pc[p] # "Accepted"))

====