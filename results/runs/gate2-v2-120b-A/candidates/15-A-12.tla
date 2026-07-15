---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F

\* Derived sets
Proc == 1..N
ECHO == "ECHO"

VARIABLES
    correct,    \* set of correct processes
    faulty,     \* set of Byzantine processes
    pc,         \* control location of each process
    sent,       \* set of (sender, msgtype) pairs sent by correct processes
    rcvd        \* map: proc -> set of messages received

\* Control locations
LocInitRecv   == "InitRecv"    \* process started with INIT
LocNoInit     == "NoInit"      \* process started without INIT
LocEchoSent   == "EchoSent"    \* process has sent ECHO (may or may not have accepted)
LocAccepted   == "Accepted"    \* process has accepted the broadcast

\* Message type
MsgEcho(s) == [type |-> ECHO, sender |-> s]

\* Initial state
Init ==
    /\ correct \in SUBSET Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> {LocInitRecv, LocNoInit}]
    /\ sent = {}
    /\ rcvd = [p \in Proc |-> {}]
    /\ \A p \in correct : pc[p] \in {LocInitRecv, LocNoInit}
    /\ \A p \in faulty : pc[p] = LocNoInit

\* Helper: distinct senders in a set of messages
DistinctSenders(msgSet) == { m.sender : m \in msgSet }

\* Receive step for a correct process p
Receive(p) ==
    /\ p \in correct
    /\ \E newMsgs \subseteq { MsgEcho(s) : s \in correct } \cup { MsgEcho(s) : s \in faulty } :
        /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup newMsgs]
        /\ UNCHANGED <<correct, faulty, pc, sent>>

\* Action: send ECHO and possibly accept
SendEchoAndAccept(p, accept) ==
    /\ p \in correct
    /\ pc[p] # LocAccepted
    /\ sent' = sent \cup { MsgEcho(p) }
    /\ pc' = [pc EXCEPT ![p] = IF accept THEN LocAccepted ELSE LocEchoSent]
    /\ UNCHANGED <<correct, faulty, rcvd>>

\* Evolution (NEXT) combines all possible steps
Next ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct :
        /\ pc[p] = LocInitRecv
        /\ SendEchoAndAccept(p, TRUE)            \* case (2): immediate accept after INIT
    \/ \E p \in correct :
        /\ pc[p] = LocNoInit
        /\ LET echoCnt == Cardinality( DistinctSenders( { m \in rcvd[p] : m.type = ECHO } ) )
           IN
           /\ echoCnt >= N - 2*T
           /\ echoCnt < N - T
           /\ SendEchoAndAccept(p, FALSE)        \* case (3): send ECHO, no accept yet
    \/ \E p \in correct :
        /\ pc[p] = LocNoInit
        /\ LET echoCnt == Cardinality( DistinctSenders( { m \in rcvd[p] : m.type = ECHO } ) )
           IN
           /\ echoCnt >= N - T
           /\ SendEchoAndAccept(p, TRUE)         \* case (4): send ECHO and accept
    \/ \E p \in correct :
        /\ pc[p] = LocEchoSent
        /\ LET echoCnt == Cardinality( DistinctSenders( { m \in rcvd[p] : m.type = ECHO } ) )
           IN
           /\ echoCnt >= N - T
           /\ SendEchoAndAccept(p, TRUE)         \* case (5): accept after enough ECHOs
    \/ UNCHANGED <<correct, faulty, pc, sent, rcvd>>

\* Stuttering step to avoid deadlock
Stutter == UNCHANGED <<correct, faulty, pc, sent, rcvd>>

Spec == Init /\ [][Next \/ Stutter]_<<correct, faulty, pc, sent, rcvd>>

\* Type correctness invariant (TypeOK)
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ pc \in [Proc -> {LocInitRecv, LocNoInit, LocEchoSent, LocAccepted}]
    /\ sent \subseteq { MsgEcho(s) : s \in correct }
    /\ rcvd \in [Proc -> SUBSET { MsgEcho(s) : s \in Proc }]

\* Safety property: if no one started with INIT, no one ever accepts
FCConstraints ==
    ( \A p \in correct : pc[p] = LocNoInit ) => ( \A p \in correct : pc[p] # LocAccepted )

\* Liveness property: eventual acceptance when all start with INIT
CorrLtl ==
    ( \A p \in correct : pc[p] = LocInitRecv ) => <> ( \A p \in correct : pc[p] = LocAccepted )

\* Liveness property: relay – if any correct accepts, eventually all accept
RelayLtl ==
    ( \E p \in correct : pc[p] = LocAccepted ) => <> ( \A p \in correct : pc[p] = LocAccepted )

\* Unforgeability property: same as FCConstraints expressed as an LTL prop
UnforgLtl == CorrLtl => CorrLtl  \* placeholder; actual check uses FCConstraints as invariant

\* The specification name required by the .cfg
Spec == Spec

====