---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* -----------------------------------------------------------------
\* Process set
\* -----------------------------------------------------------------
Proc == 1 .. N

\* -----------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------
VARIABLES 
    Correct,        \* set of correct processes
    Faulty,         \* set of faulty processes
    InitGot,        \* [Proc -> BOOLEAN] : did the process initially receive INIT?
    sentEcho,       \* [Proc -> BOOLEAN] : has the process sent an ECHO?
    accepted,       \* [Proc -> BOOLEAN] : has the process accepted?
    recv,           \* [Proc -> SUBSET Proc] : senders of ECHO messages received
    Sent            \* SUBSET Proc : correct processes that have sent an ECHO

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
vars == <<Correct, Faulty, InitGot, sentEcho, accepted, recv, Sent>>

\* -----------------------------------------------------------------
\* Initialization
\* -----------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ InitGot \in [Proc -> BOOLEAN]
    /\ sentEcho = [p \in Proc |-> FALSE]
    /\ accepted = [p \in Proc |-> FALSE]
    /\ recv = [p \in Proc |-> {}]
    /\ Sent = {}

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
\* 1. Receive a (nondeterministic) set of new ECHO messages
Receive(p) ==
    /\ p \in Correct
    /\ \E S \in SUBSET (Sent \cup Faulty) :
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup S]
    /\ UNCHANGED <<Correct, Faulty, InitGot, sentEcho, accepted, Sent>>

\* 2. If a correct process initially has INIT, it sends ECHO and accepts
InitSendAndAccept(p) ==
    /\ p \in Correct
    /\ InitGot[p] = TRUE
    /\ sentEcho[p] = FALSE
    /\ sentEcho' = [sentEcho EXCEPT ![p] = TRUE]
    /\ accepted' = [accepted EXCEPT ![p] = TRUE]
    /\ Sent' = Sent \cup {p}
    /\ UNCHANGED <<Correct, Faulty, InitGot, recv>>

\* 3. Received >= N-2T but < N-T ECHOs, send ECHO (no accept yet)
EchoIfEnoughButNotAccept(p) ==
    /\ p \in Correct
    /\ sentEcho[p] = FALSE
    /\ Cardinality(recv[p]) >= N - 2 * T
    /\ Cardinality(recv[p]) <  N - T
    /\ sentEcho' = [sentEcho EXCEPT ![p] = TRUE]
    /\ Sent' = Sent \cup {p}
    /\ UNCHANGED <<Correct, Faulty, InitGot, recv, accepted>>

\* 4. Received >= N-T ECHOs, send ECHO and accept
EchoAndAcceptIfEnough(p) ==
    /\ p \in Correct
    /\ sentEcho[p] = FALSE
    /\ Cardinality(recv[p]) >= N - T
    /\ sentEcho' = [sentEcho EXCEPT ![p] = TRUE]
    /\ accepted' = [accepted EXCEPT ![p] = TRUE]
    /\ Sent' = Sent \cup {p}
    /\ UNCHANGED <<Correct, Faulty, InitGot, recv>>

\* 5. Already sent ECHO, now enough ECHOs to accept
AcceptIfAlreadySent(p) ==
    /\ p \in Correct
    /\ sentEcho[p] = TRUE
    /\ accepted[p] = FALSE
    /\ Cardinality(recv[p]) >= N - T
    /\ accepted' = [accepted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<Correct, Faulty, InitGot, recv, sentEcho, Sent>>

\* -----------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : InitSendAndAccept(p)
    \/ \E p \in Proc : EchoIfEnoughButNotAccept(p)
    \/ \E p \in Proc : EchoAndAcceptIfEnough(p)
    \/ \E p \in Proc : AcceptIfAlreadySent(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* -----------------------------------------------------------------
\* Invariants
\* -----------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Faulty = Proc \ Correct
    /\ InitGot \in [Proc -> BOOLEAN]
    /\ sentEcho \in [Proc -> BOOLEAN]
    /\ accepted \in [Proc -> BOOLEAN]
    /\ recv \in [Proc -> SUBSET Proc]
    /\ Sent \subseteq Correct

FCConstraints == (N > 3 * T) /\ (T >= F)

\* -----------------------------------------------------------------
\* LTL properties
\* -----------------------------------------------------------------
CorrLtl ==
    ( \A p \in Correct : InitGot[p] ) => <> ( \A p \in Correct : accepted[p] )

RelayLtl ==
    ( \E p \in Correct : accepted[p] ) => <> ( \A p \in Correct : accepted[p] )

UnforgLtl ==
    ( \A p \in Correct : ~InitGot[p] ) => [] ( \A p \in Correct : ~accepted[p] )
====================================