---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (provided by the .cfg)
\* ----------------------------------------------------------------------
CONSTANT N \* total number of processes
CONSTANT T \* maximum number of Byzantine processes tolerated
CONSTANT F \* actual number of Byzantine processes (F <= T)

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Message type
\* ----------------------------------------------------------------------
MsgType == {"ECHO"}

\* A message is a pair <<sender, type>>
Msg == [sender : Proc, type : MsgType]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    correct,          \* set of correct processes
    faulty,           \* set of Byzantine processes
    pc,               \* control location of each process
    received,         \* set of messages received by each process
    sent               \* set of messages that have been sent by correct processes

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
PCIdle   == "Idle"        \* has not yet sent ECHO, not yet accepted
PCSent   == "Sent"        \* has sent ECHO, not yet accepted
PCAccept == "Accepted"    \* has accepted

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ faulty = Proc \ correct
    /\ pc = [p \in Proc |-> PCIdle]
    /\ received = [p \in Proc |-> {}]
    /\ sent = {}

\* A restricted initial state where no correct process received INIT
NoInit ==
    /\ Init
    /\ \A p \in correct : pc[p] = PCIdle

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoFrom(p) == [sender |-> p, type |-> "ECHO"]

EchoSend(p) ==
    /\ pc[p] = PCIdle
    /\ pc' = [pc EXCEPT ![p] = PCSent]
    /\ sent' = sent \cup { EchoFrom(p) }
    /\ UNCHANGED <<correct, faulty, received>>

Recv(p, msgs) ==
    /\ msgs \subseteq sent
    /\ received' = [received EXCEPT ![p] = received[p] \cup msgs]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

Accept(p) ==
    /\ pc[p] \in {PCIdle, PCSent}
    /\ pc' = [pc EXCEPT ![p] = PCAccept]
    /\ UNCHANGED <<correct, faulty, received, sent>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Action ==
    \/ \E p \in correct :
          /\ pc[p] = PCIdle
          /\ pc' = PCSent
          /\ sent' = sent \cup { EchoFrom(p) }
          /\ UNCHANGED <<correct, faulty, received, pc>>
    \/ \E p \in correct :
          /\ pc[p] = PCIdle
          /\ LET echoCount == Cardinality({ m \in received[p] : m.type = "ECHO" }) IN
             /\ echoCount >= N - 2*T
             /\ echoCount < N - T
          /\ pc' = PCSent
          /\ sent' = sent \cup { EchoFrom(p) }
          /\ UNCHANGED <<correct, faulty, received, pc>>
    \/ \E p \in correct :
          /\ pc[p] = PCIdle
          /\ LET echoCount == Cardinality({ m \in received[p] : m.type = "ECHO" }) IN
             /\ echoCount >= N - T
          /\ pc' = PCAccept
          /\ sent' = sent \cup { EchoFrom(p) }
          /\ UNCHANGED <<correct, faulty, received, pc>>
    \/ \E p \in correct :
          /\ pc[p] = PCSent
          /\ LET echoCount == Cardinality({ m \in received[p] : m.type = "ECHO" }) IN
             /\ echoCount >= N - T
          /\ pc' = PCAccept
          /\ UNCHANGED <<correct, faulty, received, sent>>
    \/ \E p \in correct, msgs \in SUBSET sent :
          /\ pc[p] \in {PCIdle, PCSent}
          /\ pc' = pc
          /\ received' = [received EXCEPT ![p] = received[p] \cup msgs]
          /\ UNCHANGED <<correct, faulty, sent>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ Action
    \/ \E p \in faulty :
          (* Byzantine processes may send arbitrary ECHO messages at any time *)
          LET bogus == EchoFrom(p) IN
          /\ sent' = sent \cup {bogus}
          /\ UNCHANGED <<correct, faulty, pc, received>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, received, sent>>

\* ----------------------------------------------------------------------
\* Type correctness (TypeOK)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ pc \in [Proc -> {PCIdle, PCSent, PCAccept}]
    /\ received \in [Proc -> SUBSET Msg]
    /\ sent \in SUBSET Msg

\* ----------------------------------------------------------------------
\* FCConstraints invariant (derived from the paper's safety constraints)
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* Safety property: Unforgeability
\* No correct process ever reaches Accepted if no correct process ever
\* received an INIT (i.e., all start in PCIdle and never send ECHO)
\* ----------------------------------------------------------------------
UnforgLtl ==
    []( \A p \in correct : pc[p] # PCAccept )

\* ----------------------------------------------------------------------
\* Liveness properties (expressed in LTL)
\* CorrLtl: if all correct processes start having received INIT (simulated
\* by starting in PCSent), then eventually all accept.
\* RelayLtl: if any correct process accepts, eventually all accept.
\* ----------------------------------------------------------------------
CorrLtl ==
    \A p \in correct : (pc[p] = PCSent) => <> ( \A q \in correct : pc[q] = PCAccept )

RelayLtl ==
    ( \E p \in correct : pc[p] = PCAccept ) => <> ( \A q \in correct : pc[q] = PCAccept )

\* ----------------------------------------------------------------------
\* Theorem (optional, for TLC to know the invariant we care about)
\* ----------------------------------------------------------------------
THEOREM Spec => []UnforgLtl

====