---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Variables (renamed to avoid clash with potential reserved identifiers)
\* ----------------------------------------------------------------------
VARIABLES CSet, FSet, initRecv, sent, accepted, recv

vars == <<CSet, FSet, initRecv, sent, accepted, recv>>

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ CSet \subseteq Proc
    /\ Cardinality(CSet) = N - F
    /\ FSet = Proc \ CSet
    /\ initRecv \subseteq CSet
    /\ sent \subseteq CSet
    /\ accepted \subseteq CSet
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
    /\ CSet \subseteq Proc
    /\ Cardinality(CSet) = N - F
    /\ FSet = Proc \ CSet
    /\ initRecv \subseteq CSet
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
    /\ p \in CSet
    /\ S \subseteq Proc \ recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup S]
    /\ UNCHANGED <<CSet, FSet, initRecv, sent, accepted>>

\* (2) Send ECHO without immediate acceptance
SendEchoOnly(p) ==
    /\ p \in CSet
    /\ p \notin sent
    /\ p \notin initRecv
    /\ EchoCount(p) >= N - 2 * T
    /\ EchoCount(p) <  N - T
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<CSet, FSet, initRecv, accepted, recv>>

\* (3) Send ECHO and accept (covers init‑receivers and strong quorum)
SendEchoAndAccept(p) ==
    /\ p \in CSet
    /\ p \notin sent
    /\ (p \in initRecv) \/ (EchoCount(p) >= N - T)
    /\ sent' = sent \cup {p}
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<CSet, FSet, initRecv, recv>>

\* (4) Accept after having already sent ECHO
AcceptOnly(p) ==
    /\ p \in CSet
    /\ p \in sent
    /\ p \notin accepted
    /\ EchoCount(p) >= N - T
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<CSet, FSet, initRecv, sent, recv>>

\* ----------------------------------------------------------------------
\* Next relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in CSet: \E S \in SUBSET (Proc \ recv[p]) : Receive(p, S)
    \/ \E p \in CSet: SendEchoOnly(p)
    \/ \E p \in CSet: SendEchoAndAccept(p)
    \/ \E p \in CSet: AcceptOnly(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
\* Correctness: if all correct processes start with INIT, eventually all accept
CorrLtl == []( (initRecv = CSet) => <> (accepted = CSet) )

\* Relay: if any correct process accepts, eventually all accept
RelayLtl == []( ( \E p \in CSet : p \in accepted ) => <> (accepted = CSet) )

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