---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc   == 1..N                         \* universe of process identifiers
Msg    == {"ECHO"}                     \* only one message type

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    correct,         \* set of correct processes
    faulty,          \* set of Byzantine processes (complement of correct)
    pc,              \* control location of each process
    sent,            \* set of messages sent by correct processes
    received         \* map: proc -> set of messages (sender, type)

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
Locs == {"InitYes", "InitNo", "EchoSent", "Accepted"}

\* ----------------------------------------------------------------------
\* Types predicate (used for TypeOK invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty  = Proc \ correct
    /\ pc \in [Proc -> Locs]
    /\ sent \subseteq Proc \X Msg
    /\ received \in [Proc -> SUBSET (Proc \X Msg)]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ReceivedEchoFrom(p) ==
    { q \in Proc : <<q, "ECHO">> \in received[p] }

IsFaulty(p) == p \in faulty

EchoFromCorrect(p) ==
    { q \in correct : <<q, "ECHO">> \in received[p] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ faulty = Proc \ correct
    /\ pc = [p \in Proc |-> IF p \in correct THEN "InitNo" ELSE "InitNo"]
    /\ sent = {}
    /\ received = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Correct process receives any subset of messages that have been sent
\*    (including possibly messages from faulty processes, modeled nondet.)
Receive(p) ==
    /\ p \in correct
    /\ \E newRecv \subseteq (sent \cup {<<q, "ECHO">> : q \in faulty}) :
        /\ received' = [received EXCEPT ![p] = received[p] \cup newRecv]
        /\ UNCHANGED <<correct, faulty, pc, sent>>

\* 2. If a correct process started with INIT (broadcast state) it accepts and sends ECHO
AcceptAndEchoFromInit(p) ==
    /\ p \in correct
    /\ pc[p] = "InitYes"
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, received>>

\* 3. If a correct process (not yet sent ECHO) receives >= N-2T distinct ECHOs,
\*    it sends ECHO but does not yet accept.
SendEchoNoAccept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"InitNo", "EchoSent"}
    /\ /\ pc[p] = "InitNo"
       \/ pc[p] = "EchoSent"
    /\ Cardinality(EchoFromCorrect(p)) >= N - 2*T
    /\ Cardinality(EchoFromCorrect(p)) < N - T
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
    /\ UNCHANGED <<correct, faulty, received>>

\* 4. If a correct process (not yet sent ECHO) receives >= N-T distinct ECHOs,
\*    it sends ECHO and accepts.
SendEchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"InitNo", "EchoSent"}
    /\ Cardinality(EchoFromCorrect(p)) >= N - T
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, received>>

\* 5. If a correct process already sent ECHO receives >= N-T distinct ECHOs,
\*    it accepts.
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "EchoSent"
    /\ Cardinality(EchoFromCorrect(p)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, sent, received>>

\* 6. Byzantine processes may nondeterministically send arbitrary ECHO messages
ByzSendEcho(p) ==
    /\ p \in faulty
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, pc, received>>

\* Combined step for a correct process
CorrectStep ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct : AcceptAndEchoFromInit(p)
    \/ \E p \in correct : SendEchoNoAccept(p)
    \/ \E p \in correct : SendEchoAndAccept(p)
    \/ \E p \in correct : AcceptAfterEcho(p)

\* Combined step for a Byzantine process
ByzStep ==
    \E p \in faulty : ByzSendEcho(p)

Next == CorrectStep \/ ByzStep

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, sent, received>>

\* ----------------------------------------------------------------------
\* Safety invariant: FCConstraints (unforgeability)
\*   No correct process ever reaches "Accepted" when no correct process
\*   started with the broadcast INIT (i.e., all correct processes start in "InitNo").
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ \A p \in correct : pc[p] \in {"InitNo", "EchoSent", "Accepted"}
    /\ ( \A p \in correct : pc[p] = "InitNo" ) => \A p \in correct : pc[p] # "Accepted"

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl ==
    /\ \A p \in correct : pc[p] = "InitYes"
    => <> ( \A p \in correct : pc[p] = "Accepted" )

RelayLtl ==
    /\ \E p \in correct : pc[p] = "Accepted"
    => <> ( \A p \in correct : pc[p] = "Accepted" )

UnforgLtl ==
    /\ \A p \in correct : pc[p] = "InitNo"
    => [] ( \A p \in correct : pc[p] # "Accepted" )

=============================================================================