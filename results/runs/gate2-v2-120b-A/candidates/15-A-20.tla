---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F

ASSUME N > 3 * T
ASSUME T >= F
ASSUME F >= 0

VARIABLES
    correct,          \* Set of correct processes
    faulty,           \* Set of Byzantine processes
    pc,               \* Control location per process
    recv,             \* Received messages per process (set of [type |-> "ECHO", sender |-> Proc])
    sent               \* Set of ECHO messages sent by correct processes

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
Proc == 1..N
Msg  == [type : {"ECHO"}, sender : Proc]

PCValues == {"init", "nosend", "sent", "accepted"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ correct \in SUBSET Proc
    /\ Cardinality(correct) = N - F
    /\ faulty = Proc \ correct
    /\ pc = [p \in Proc |-> IF p \in correct THEN "nosend" ELSE "init"]
         \* Correct processes start in "nosend" (no INIT received).
         \* Faulty processes start in "init" (they may behave arbitrarily).
    /\ recv = [p \in Proc |-> {}]
    /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Receive arbitrary subset of already sent messages, plus any messages
\*    the modeler may allow from Byzantine processes (we allow any Msg from
\*    any process, modelling Byzantine flooding).
Receive(p) ==
    /\ p \in correct
    /\ UNCHANGED <<correct, faulty, pc, sent>>
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup
               { m \in sent \cup { [type |-> "ECHO", sender |-> b] :
                                   b \in Proc } :
                 m \notin recv[p] }]

\* 2. If a correct process has received INIT (modeled as pc = "init")
\*    it immediately accepts and sends an ECHO.
InitAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "init"
    /\ pc'   = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<recv, correct, faulty>>

\* 3. If a correct process has not yet sent ECHO and receives at least N-2T
\*    distinct ECHO messages (but fewer than N-T), it sends its ECHO
\*    but does not yet accept.
EchoNoAccept(p) ==
    LET echos == { m \in recv[p] : m.type = "ECHO" } IN
    /\ p \in correct
    /\ pc[p] = "nosend"
    /\ Cardinality({ m.sender : m \in echos }) >= N - 2 * T
    /\ Cardinality({ m.sender : m \in echos }) < N - T
    /\ pc'   = [pc EXCEPT ![p] = "sent"]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<recv, correct, faulty>>

\* 4. If a correct process has not yet sent ECHO and receives at least N-T
\*    distinct ECHO messages, it sends its ECHO and immediately accepts.
EchoAccept(p) ==
    LET echos == { m \in recv[p] : m.type = "ECHO" } IN
    /\ p \in correct
    /\ pc[p] \in {"nosend", "sent"}
    /\ Cardinality({ m.sender : m \in echos }) >= N - T
    /\ pc'   = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<recv, correct, faulty>>

\* 5. If a correct process has already sent ECHO and later receives at least N-T
\*    distinct ECHO messages, it accepts.
AcceptAfterEcho(p) ==
    LET echos == { m \in recv[p] : m.type = "ECHO" } IN
    /\ p \in correct
    /\ pc[p] = "sent"
    /\ Cardinality({ m.sender : m \in echos }) >= N - T
    /\ pc'   = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<recv, sent, correct, faulty>>

\* Weak fairness assumption (not an action, used in the .cfg):
\*   WF_vars(Receive(p))

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct : InitAccept(p)
    \/ \E p \in correct : EchoNoAccept(p)
    \/ \E p \in correct : EchoAccept(p)
    \/ \E p \in correct : AcceptAfterEcho(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, recv, sent, correct, faulty>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (TypeOK)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ pc \in [Proc -> PCValues]
    /\ recv \in [Proc -> SUBSET Msg]
    /\ sent \subseteq Msg

\* ----------------------------------------------------------------------
\* Fault‑containment invariant (FCConstraints)
\*   No correct process may accept unless it either started with INIT
\*   or has observed enough ECHO messages.
\* ----------------------------------------------------------------------
FCConstraints ==
    \A p \in correct :
        pc[p] = "accepted" =>
            \/ pc[p] = "init"
            \/ ( Cardinality({ m.sender : m \in recv[p] /\ m.type = "ECHO" }) >= N - T )
            \/ ( Cardinality({ m.sender : m \in recv[p] /\ m.type = "ECHO" }) >= N - 2 * T
                 /\ pc[p] = "sent" ) \* already covered by the previous line, but kept for clarity

\* ----------------------------------------------------------------------
\* Liveness properties
\*   CorrLtl  : If all correct processes start with INIT, eventually all accept.
\*   RelayLtl : If any correct process accepts, eventually all accept.
\*   UnforgLtl: If no correct process starts with INIT, never any accept.
\* ----------------------------------------------------------------------
CorrLtl ==
    ( \A p \in correct : pc[p] = "init" ) => <> ( \A p \in correct : pc[p] = "accepted" )

RelayLtl ==
    ( \E p \in correct : pc[p] = "accepted" ) => <> ( \A p \in correct : pc[p] = "accepted" )

UnforgLtl ==
    ( \A p \in correct : pc[p] = "nosend" ) => [] ( \A p \in correct : pc[p] # "accepted" )

=============================================================================