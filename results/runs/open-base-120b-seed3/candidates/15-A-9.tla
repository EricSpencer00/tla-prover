---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES Correct, Faulty, Sent, Recv, pc

\* ----------------------------------------------------------------------
\* Process set
Proc == 1 .. N

\* All possible ECHO messages (from any process)
AllMsg == { [type |-> "ECHO", from |-> q] : q \in Proc }

\* ----------------------------------------------------------------------
\* Helper definitions
EchoSenders(p) == { m.from : m \in Recv[p] }

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ Sent = {}
    /\ Recv = [p \in Proc |-> {}]
    /\ pc \in [Proc -> {"InitRec", "NoInit"}]

\* ----------------------------------------------------------------------
\* Actions

\* A correct process may receive any (new) set of messages
Receive(p) ==
    /\ p \in Correct
    /\ \E newSet \in SUBSET (AllMsg \ Recv[p]) :
          /\ Recv' = [Recv EXCEPT ![p] = Recv[p] \cup newSet]
          /\ UNCHANGED <<Correct, Faulty, Sent, pc>>

\* Correct process (no INIT) receives enough ECHOs (>= N-2T, < N-T) and sends ECHO
SendEcho(p) ==
    LET cnt == Cardinality(EchoSenders(p)) IN
    /\ p \in Correct
    /\ pc[p] = "NoInit"
    /\ cnt >= N - 2 * T
    /\ cnt < N - T
    /\ Sent' = Sent \cup { [type |-> "ECHO", from |-> p] }
    /\ pc'   = [pc EXCEPT ![p] = "SentEcho"]
    /\ UNCHANGED <<Correct, Faulty, Recv>>

\* Correct process (no INIT) receives enough ECHOs (>= N-T) and sends ECHO and accepts
SendEchoAccept(p) ==
    LET cnt == Cardinality(EchoSenders(p)) IN
    /\ p \in Correct
    /\ pc[p] = "NoInit"
    /\ cnt >= N - T
    /\ Sent' = Sent \cup { [type |-> "ECHO", from |-> p] }
    /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<Correct, Faulty, Recv>>

\* Correct process that already received INIT immediately sends ECHO and accepts
SendEchoAndAcceptInit(p) ==
    /\ p \in Correct
    /\ pc[p] = "InitRec"
    /\ Sent' = Sent \cup { [type |-> "ECHO", from |-> p] }
    /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<Correct, Faulty, Recv>>

\* Correct process that has already sent ECHO and now sees enough ECHOs (>= N-T) accepts
AcceptOnly(p) ==
    LET cnt == Cardinality(EchoSenders(p)) IN
    /\ p \in Correct
    /\ pc[p] = "SentEcho"
    /\ cnt >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<Correct, Faulty, Sent, Recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : SendEcho(p)
    \/ \E p \in Correct : SendEchoAccept(p)
    \/ \E p \in Correct : SendEchoAndAcceptInit(p)
    \/ \E p \in Correct : AcceptOnly(p)

\* Variables tuple for temporal operators
vars == <<Correct, Faulty, Sent, Recv, pc>>

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ Sent \subseteq { [type |-> "ECHO", from |-> q] : q \in Correct }
    /\ Recv \in [Proc -> SUBSET AllMsg]
    /\ pc \in [Proc -> {"InitRec", "NoInit", "SentEcho", "Accepted"}]

\* ----------------------------------------------------------------------
\* Fault‑containment constraints
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties

\* If all correct processes start having received INIT, eventually all accept
CorrLtl == ( \A p \in Correct : pc[p] = "InitRec" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

\* If any correct process accepts, eventually all correct processes accept
RelayLtl == ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

\* If no correct process starts with INIT, then no correct process ever accepts
UnforgLtl == ( \A p \in Correct : pc[p] = "NoInit" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

====