---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be bound in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N
CONSTANT T
CONSTANT F

\* Derived constant: number of correct processes
CONSTANT CorrectCount \* = N - F  (just for readability; not used directly)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N
CorrectProc == { p \in Proc : p \in Correct }
FaultyProc  == { p \in Proc : p \in Faulty }

MessageType == {"ECHO"}

\* Full message: a pair <<sender, type>>
Msg == [sender : Proc, type : MessageType]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    correct,        \* set of correct processes
    faulty,         \* set of faulty processes
    pc,             \* control location of each process
    received,       \* set of messages each process has received
    sent             \* set of messages sent by correct processes

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PCValues == {"StartNoInit", "StartInit", "SentEcho", "Accepted"}

\* ECHO messages that a process has received from distinct senders
EchoesFrom(p) == { m.sender : m \in received[p] /\ m.type = "ECHO" }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ correct = { p \in Proc : p \notin faulty }   \* will be constrained by TypeOK
    /\ faulty  = { p \in Proc : p \in faulty }     \* same as above
    /\ pc = [p \in Proc |-> 
            IF p \in correct 
                THEN IF InitHasMessage(p) THEN "StartInit" ELSE "StartNoInit"
                ELSE "StartNoInit"]
    /\ received = [p \in Proc |-> {}]
    /\ sent = {}

\* Whether process p is assumed to have received the broadcaster's INIT
InitHasMessage(p) == FALSE   \* (non‑broadcast scenario).  For the broadcast
                              \* scenario we will use a separate InitAlt.

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Receive new messages (any subset of currently sent messages plus any from
\*    Byzantine processes)
Receive(p) ==
    /\ p \in correct
    /\ \E new \in SUBSET (sent \cup 
               { [sender |-> b, type |-> "ECHO"] : b \in faulty }) :
          /\ received' = [received EXCEPT ![p] = received[p] \cup new]
          /\ UNCHANGED <<correct, faulty, pc, sent>>

\* 2. If a correct process starts with the INIT message, it immediately sends
\*    an ECHO and accepts.
BroadcastAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "StartInit"
    /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, received>>

\* 3. Correct process not yet sent ECHO receives >= N-2T distinct ECHO, but < N-T
SendEchoNoAccept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"StartNoInit", "StartInit"}
    /\ LET n == Cardinality(EchoesFrom(p)) IN
          /\ n >= N - 2*T
          /\ n < N - T
    /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
    /\ pc'   = [pc EXCEPT ![p] = "SentEcho"]
    /\ UNCHANGED <<correct, faulty, received>>

\* 4. Correct process not yet sent ECHO receives >= N-T distinct ECHO
SendEchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"StartNoInit", "StartInit"}
    /\ Cardinality(EchoesFrom(p)) >= N - T
    /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
    /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, received>>

\* 5. Correct process that has already sent ECHO receives >= N-T distinct ECHO
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "SentEcho"
    /\ Cardinality(EchoesFrom(p)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, received, sent>>

\* 6. Byzantine processes may arbitrarily send messages (modeled as nondet)
ByzSend ==
    /\ \E b \in faulty :
          sent' = sent \cup { [sender |-> b, type |-> "ECHO"] }
    /\ UNCHANGED <<correct, faulty, pc, received>>

\* Combined next-state relation
Next ==
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : BroadcastAccept(p)
    \/ \E p \in Proc : SendEchoNoAccept(p)
    \/ \E p \in Proc : SendEchoAndAccept(p)
    \/ \E p \in Proc : AcceptAfterEcho(p)
    \/ ByzSend

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, received, sent>>

\* ----------------------------------------------------------------------
\* Safety invariant: Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty  \subseteq Proc
    /\ correct \cap faulty = {}
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty)  = F
    /\ pc \in [Proc -> PCValues]
    /\ received \in [Proc -> SUBSET Msg]
    /\ sent \in SUBSET Msg
    /\ \A m \in sent : m.type = "ECHO"

\* ----------------------------------------------------------------------
\* Safety invariant: FCConstraints (captures the two safety properties)
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ \A p \in correct : pc[p] \in {"StartNoInit", "StartInit", "SentEcho", "Accepted"}
    /\ ( \A p \in correct : pc[p] = "Accepted" => Cardinality({ q \in correct : pc[q] = "Accepted" }) >= N - T )
    /\ ( \A p \in correct : pc[p] = "SentEcho" => Cardinality({ q \in correct : "ECHO" \in { m.type : m \in received[p] } }) >= N - 2*T )
    /\ ( \A p \in correct : pc[p] = "StartNoInit" => \A q \in correct : "ECHO" \notin { m.type : m \in received[p] } )
    /\ ( \A p \in correct : pc[p] = "StartInit" => pc[p] = "Accepted" ) \* unforgeability under no‑INIT scenario

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl == []( ( \A p \in correct : pc[p] = "StartInit" ) => <> ( \A p \in correct : pc[p] = "Accepted" ) )
RelayLtl == []( ( \E p \in correct : pc[p] = "Accepted" ) => <> ( \A p \in correct : pc[p] = "Accepted" ) )
UnforgLtl == []( ( \A p \in correct : pc[p] = "StartNoInit" ) => [] ( \A p \in correct : pc[p] # "Accepted" ) )

=============================================================================