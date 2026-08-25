---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1..N
MsgType == {"ECHO"}
Message == [sender : Proc, type : MsgType]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, pc, recv, sent

vars == <<Correct, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Faulty == Proc \ Correct

\* Set of all possible ECHO messages that a correct process may have sent
SentEchos == sent

\* For a process p, the set of senders from which p has received an ECHO
EchoSenders(p) == { m.sender : m \in recv[p] }

\* Cardinality of a set (using the built‑in function Cardinality)
Card(s) == Cardinality(s)

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Card(Correct) = N - F
    /\ pc = [p \in Proc |-> 
               IF p \in Correct 
               THEN IF RandomChoice({ "NoInit", "InitRec"}) = "InitRec"
                    THEN "InitRec"
                    ELSE "NoInit"
               ELSE "NoInit"]
    /\ recv = [p \in Proc |-> {}]
    /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ReceiveAndAct(p) ==
    /\ p \in Correct
    /\ \* nondeterministically receive any new messages
       LET possibleMsgs == SentEchos \cup (Faulty \X {"ECHO"}) IN
       \E newMsgs \subseteq possibleMsgs :
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup 
                      { [sender |-> s, type |-> "ECHO"] : s \in newMsgs } ]
    /\ (* compute number of distinct ECHO senders after receiving *)
       cnt == Card(EchoSenders(p) )
    /\ CASE 
        pc[p] = "InitRec" ->
            /\ pc' = [pc EXCEPT ![p] = "Accepted"]
            /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
        pc[p] = "NoInit" /\ cnt >= N - T ->
            /\ pc' = [pc EXCEPT ![p] = "Accepted"]
            /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
        pc[p] = "NoInit" /\ cnt >= N - 2*T /\ cnt < N - T ->
            /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
            /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
        pc[p] = "EchoSent" /\ cnt >= N - T ->
            /\ pc' = [pc EXCEPT ![p] = "Accepted"]
            /\ UNCHANGED sent
        OTHER ->
            /\ UNCHANGED <<pc, sent>>
    /\ UNCHANGED <<Correct, recv>>

Next ==
    \/ \E p \in Correct : ReceiveAndAct(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
    /\ \A p \in Correct : WF_vars(ReceiveAndAct(p))

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Card(Correct) = N - F
    /\ pc \in [Proc -> {"NoInit","InitRec","EchoSent","Accepted"}]
    /\ recv \in [Proc -> SUBSET Message]
    /\ sent \subseteq { [sender |-> s, type |-> "ECHO"] : s \in Correct }

\* ----------------------------------------------------------------------
\* Fault‑correctness constraints
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
AllInit == \A p \in Correct : pc[p] = "InitRec"
AllNoInit == \A p \in Correct : pc[p] = "NoInit"
AllAccepted == \A p \in Correct : pc[p] = "Accepted"
SomeAccepted == \E p \in Correct : pc[p] = "Accepted"

CorrLtl == [] (AllInit => <> AllAccepted)
RelayLtl == [] (SomeAccepted => <> AllAccepted)
UnforgLtl == [] (AllNoInit => [] ( \A p \in Correct : pc[p] # "Accepted"))

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* CONSTANTS   N, T, F
\* SPECIFICATION  Spec
\* INVARIANTS    TypeOK, FCConstraints
\* PROPERTIES    CorrLtl, RelayLtl, UnforgLtl
=============================================================================