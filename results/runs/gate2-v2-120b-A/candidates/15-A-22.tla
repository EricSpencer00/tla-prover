---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be set in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N \* total number of processes
CONSTANT T \* maximum number of Byzantine processes tolerated
CONSTANT F \* actual number of Byzantine processes (F <= T)

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

\* Message type (only ECHO is used in this protocol)
MsgType == {"ECHO"}

\* Message is a pair <<sender, type>>
Message == [sender : Proc, type : MsgType]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    correct,          \* set of correct processes
    faulty,           \* set of Byzantine processes
    pc,               \* control location of each process
    recv,             \* messages received by each process
    sent               \* messages sent by correct processes

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
PCInitNo   == "InitNo"    \* correct process did NOT receive INIT
PCInitYes  == "InitYes"   \* correct process DID receive INIT (broadcast state)
PCEchoSent == "EchoSent"  \* correct process has already sent its ECHO
PCAccepted == "Accepted"  \* correct process has accepted

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F
    /\ pc = [p \in correct |-> IF p \in InitYesSet THEN PCInitYes ELSE PCInitNo]
    /\ recv = [p \in correct |-> {}]
    /\ sent = {}

\* InitYesSet selects the processes that start having received the broadcaster's
\* INIT message.  In the full model this set is nondeterministic; for the
\* restricted no‑broadcast model it is empty (see later).
InitYesSet == {}    \* will be overridden by a separate InitNoBroadcast definition

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Echo(p) == [sender |-> p, type |-> "ECHO"]
EchoFrom(senders) == { Echo(p) : p \in senders }

\* Number of distinct ECHO messages received by process p
EchoCount(p) == Cardinality({ m \in recv[p] : m.type = "ECHO" })

\* Distinct senders of ECHO messages received by process p
EchoSenders(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in correct
    /\ \E newMsgs \subseteq (sent \cup { Echo(b) : b \in faulty }) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
        /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] = PCInitNo \/ pc[p] = PCEchoSent
    /\ sent' = sent \cup { Echo(p) }
    /\ UNCHANGED <<correct, faulty, pc, recv>>

Accept(p) ==
    /\ p \in correct
    /\ pc[p] # PCAccepted
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, sent, recv>>

Act(p) ==
    \/ /\ pc[p] = PCInitYes
       /\ SendEcho(p)
       /\ Accept(p)          \* immediate accept after sending ECHO
    \/ /\ pc[p] = PCInitNo
       /\ IF EchoCount(p) >= N - T
          THEN /\ SendEcho(p) /\ Accept(p)
          ELSE IF EchoCount(p) >= N - 2*T
               THEN /\ SendEcho(p)
               ELSE UNCHANGED <<pc, sent>>
    \/ /\ pc[p] = PCEchoSent
       /\ IF EchoCount(p) >= N - T
          THEN Accept(p)
          ELSE UNCHANGED <<pc>>

Next ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct : Act(p)
    \/ UNCHANGED <<correct, faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, recv, sent, correct, faulty>>

\* ----------------------------------------------------------------------
\* Type correctness (invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F
    /\ pc \in [correct -> {"InitNo", "InitYes", "EchoSent", "Accepted"}]
    /\ recv \in [correct -> SUBSET Message]
    /\ sent \subseteq { Echo(p) : p \in correct }

\* ----------------------------------------------------------------------
\* Fault‑constrained invariant (FCConstraints)
\*   – No correct process accepts unless it has either started in the
\*     broadcast state or has received enough ECHO messages.
\*   – The number of ECHO messages sent never exceeds the number of correct
\*     processes.
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ \A p \in correct :
        (pc[p] = "Accepted") =>
            (   pc[p] = "InitYes"
             \/ EchoCount(p) >= N - 2*T )
    /\ Cardinality(sent) <= Cardinality(correct)

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl == []<>(\A p \in correct : pc[p] = "Accepted")
RelayLtl == []((\E p \in correct : pc[p] = "Accepted") => <> (\A p \in correct : pc[p] = "Accepted"))
UnforgLtl == [](\A p \in correct : pc[p] # "Accepted")

\* ----------------------------------------------------------------------
\* Variant for the no‑broadcast safety check (all correct processes start
\* without INIT).  This overrides InitYesSet to be empty, effectively making
\* every correct process start in the "InitNo" state.
\* ----------------------------------------------------------------------
InitNoBroadcast ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F
    /\ pc = [p \in correct |-> PCInitNo]
    /\ recv = [p \in correct |-> {}]
    /\ sent = {}

\* ----------------------------------------------------------------------
\* Specification for the safety‑only configuration
\* ----------------------------------------------------------------------
SpecNoBroadcast == InitNoBroadcast /\ [][Next]_<<pc, recv, sent, correct, faulty>>

=============================================================================