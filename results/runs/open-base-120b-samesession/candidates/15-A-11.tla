---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANT N, T, F

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

\* ----------------------------------------------------------------------
\* TYPE DEFINITIONS
\* ----------------------------------------------------------------------
PCVals == {"Init", "NoInit", "EchoSent", "Accepted"}

Message == [type : {"ECHO"}, from : 1..N]

\* ----------------------------------------------------------------------
\* HELPERS
\* ----------------------------------------------------------------------
CorrectSet == 1..N
InitState   == "Init"
NoInitState == "NoInit"
EchoSentState == "EchoSent"
AcceptState == "Accepted"

\* Number of distinct senders of ECHO messages that a process p has received
EchoSenders(p) == { m.from : m \in recv[p] }

\* Whether process p (correct) has already sent its ECHO
HasEcho(p) == p \in { m.from : m \in sent }

\* ----------------------------------------------------------------------
\* INVARIANTS
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq CorrectSet
    /\ Cardinality(Correct) = N - F
    /\ Faulty = CorrectSet \ Correct
    /\ pc \in [Correct -> PCVals]
    /\ sent \subseteq { [type |-> "ECHO", from |-> p] : p \in Correct }
    /\ recv \in [CorrectSet -> SUBSET Message]

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq CorrectSet
    /\ Cardinality(Correct) = N - F
    /\ Faulty = CorrectSet \ Correct
    /\ \* each correct process starts either in Init or NoInit state
       pc = [p \in Correct |-> 
                IF RandomElement(PCVals) = InitState THEN InitState ELSE NoInitState]
    /\ sent = {}
    /\ recv = [p \in CorrectSet |-> {}]

\* ----------------------------------------------------------------------
\* ACTIONS
\* ----------------------------------------------------------------------
\* Correct process p may receive any subset of messages that are
\* already sent by correct processes or arbitrary ECHO messages from
\* Byzantine senders.
Receive(p) ==
    /\ p \in Correct
    /\ LET possible == sent \cup 
                        { [type |-> "ECHO", from |-> f] : f \in Faulty }
         newMsgs  == possible \ recv[p]
         add      == CHOOSE s \subseteq newMsgs : TRUE
       IN
          /\ add \subseteq newMsgs
          /\ recv' = [recv EXCEPT ![p] = @ \cup add]
          /\ UNCHANGED <<Correct, Faulty, pc, sent>>

\* Action for sending ECHO and possibly accepting, depending on conditions
Send(p) ==
    /\ p \in Correct
    /\ LET cnt == Cardinality(EchoSenders(p)) IN
       \/ /\ pc[p] = InitState
          /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
          /\ pc' = [pc EXCEPT ![p] = AcceptState]
          /\ UNCHANGED recv
       \/ /\ pc[p] = NoInitState /\ ~HasEcho(p) /\ cnt >= N - 2*T /\ cnt < N - T
          /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
          /\ pc'   = [pc EXCEPT ![p] = EchoSentState]
          /\ UNCHANGED recv
       \/ /\ pc[p] = NoInitState /\ ~HasEcho(p) /\ cnt >= N - T
          /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
          /\ pc'   = [pc EXCEPT ![p] = AcceptState]
          /\ UNCHANGED recv
       \/ /\ pc[p] = EchoSentState /\ cnt >= N - T
          /\ pc' = [pc EXCEPT ![p] = AcceptState]
          /\ UNCHANGED <<sent, recv>>
    /\ UNCHANGED <<Correct, Faulty>>

\* Next step is either a receive or a send by some correct process
Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : Send(p)

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Correct, Faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\* STATE PREDICATES FOR PROPERTIES
\* ----------------------------------------------------------------------
AllInit  == \A p \in Correct : pc[p] = InitState
AllNoInit == \A p \in Correct : pc[p] = NoInitState
AllAccepted == \A p \in Correct : pc[p] = AcceptState
SomeAccepted == \E p \in Correct : pc[p] = AcceptState

\* ----------------------------------------------------------------------
\* PROPERTIES (LTL)
\* ----------------------------------------------------------------------
CorrLtl  == [] ( AllInit => <> AllAccepted )
RelayLtl == [] ( SomeAccepted => <> AllAccepted )
UnforgLtl == [] ( AllNoInit => [] ( ~SomeAccepted ) )

=============================================================================