---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, initRecv, sent, accepted, recv

vars == <<Correct, Faulty, initRecv, sent, accepted, recv>>

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ initRecv \subseteq Correct
    /\ sent \subseteq Correct
    /\ accepted \subseteq Correct
    /\ recv \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc: recv[p] \subseteq Proc

\* ----------------------------------------------------------------------
\* Fault‑tolerance constraints
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ initRecv \subseteq Correct
    /\ sent = {}
    /\ accepted = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper: number of distinct ECHO senders known to p
\* ----------------------------------------------------------------------
EchoCount(p) == Cardinality(recv[p])

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* (1) Receive a (possibly empty) set of new ECHO messages
Receive(p, S) ==
    /\ p \in Correct
    /\ S \subseteq Proc \ recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup S]
    /\ UNCHANGED <<Correct, Faulty, initRecv, sent, accepted>>

\* (2) Send ECHO without immediate acceptance
SendEchoOnly(p) ==
    /\ p \in Correct
    /\ p \notin sent
    /\ p \notin initRecv
    /\ EchoCount(p) >= N - 2 * T
    /\ EchoCount(p) <  N - T
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<Correct, Faulty, initRecv, accepted, recv>>

\* (3) Send ECHO and accept (covers init‑receivers and strong quorum)
SendEchoAndAccept(p) ==
    /\ p \in Correct
    /\ p \notin sent
    /\ (p \in initRecv) \/ (EchoCount(p) >= N - T)
    /\ sent' = sent \cup {p}
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<Correct, Faulty, initRecv, recv>>

\* (4) Accept after having already sent ECHO
AcceptOnly(p) ==
    /\ p \in Correct
    /\ p \in sent
    /\ p \notin accepted
    /\ EchoCount(p) >= N - T
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<Correct, Faulty, initRecv, sent, recv>>

\* ----------------------------------------------------------------------
\* Next relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Correct: \E S \in SUBSET (Proc \ recv[p]) : Receive(p, S)
    \/ \E p \in Correct: SendEchoOnly(p)
    \/ \E p \in Correct: SendEchoAndAccept(p)
    \/ \E p \in Correct: AcceptOnly(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
\* Correctness: if all correct processes start with INIT, eventually all accept
CorrLtl == []( (initRecv = Correct) => <> (accepted = Correct) )

\* Relay: if any correct process accepts, eventually all accept
RelayLtl == []( ( \E p \in Correct : p \in accepted ) => <> (accepted = Correct) )

\* Unforgeability: if no correct process starts with INIT, no correct ever accepts
UnforgLtl == []( (initRecv = {}) => [] (accepted = {}) )

\* ----------------------------------------------------------------------
\* Theorems (optional, for TLC checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints
THEOREM Spec => CorrLtl
THEOREM Spec => RelayLtl
THEOREM Spec => UnforgLtl

====