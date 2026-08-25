---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be supplied in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1 .. N
AllMsgs == { <<i, "ECHO">> : i \in Proc }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, faulty, pc, sent, rec

vars == << Correct, faulty, pc, sent, rec >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SenderSet(p) == { s \in Proc : <<s, "ECHO">> \in rec[p] }
Cnt(p) == Cardinality( SenderSet(p) )

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ faulty = Proc \ Correct
    /\ pc \in [Proc -> {"InitRec", "NoInit"}]   \* correct processes may start with or without INIT
    /\ sent = {}
    /\ rec = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in Correct
    /\ rec' = [rec EXCEPT ![p] = rec[p] \cup (sent \cup AllMsgs)]
    /\ UNCHANGED << Correct, faulty, pc, sent >>

SendEcho(p) ==
    /\ p \in Correct
    /\ <<p, "ECHO">> \notin sent
    /\ pc[p] = "NoInit"
    /\ N - 2*T <= Cnt(p) /\ Cnt(p) < N - T
    /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ UNCHANGED << Correct, faulty, rec >>

SendEchoAndAccept(p) ==
    /\ p \in Correct
    /\ <<p, "ECHO">> \notin sent
    /\ \/
        /\ pc[p] = "InitRec"
        \/ /\ pc[p] = "NoInit"
           /\ Cnt(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ UNCHANGED << Correct, faulty, rec >>

Accept(p) ==
    /\ p \in Correct
    /\ pc[p] = "EchoSent"
    /\ Cnt(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED << Correct, faulty, sent, rec >>

Next ==
    \E p \in Proc :
        \/ Receive(p)
        \/ SendEcho(p)
        \/ SendEchoAndAccept(p)
        \/ Accept(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ faulty = Proc \ Correct
    /\ pc \in [Proc -> {"InitRec", "NoInit", "EchoSent", "Accepted"}]
    /\ sent \subseteq AllMsgs
    /\ rec \in [Proc -> SUBSET AllMsgs]

\* ----------------------------------------------------------------------
\* Fault‑containment constraints
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ Cardinality(Correct) = N - F
    /\ Cardinality(faulty)   = F
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* State predicates used in LTL properties
\* ----------------------------------------------------------------------
AllInit == \A p \in Correct : pc[p] = "InitRec"
AllNoInit == \A p \in Correct : pc[p] = "NoInit"
AllAccepted == \A p \in Correct : pc[p] = "Accepted"
SomeAccepted == \E p \in Correct : pc[p] = "Accepted"

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == [] (AllInit => <> AllAccepted)
RelayLtl == [] (SomeAccepted => <> AllAccepted)
UnforgLtl == [] (AllNoInit => [] ( \A p \in Correct : pc[p] # "Accepted" ))

\* ----------------------------------------------------------------------
\* Theorem statements (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints
THEOREM Spec => CorrLtl
THEOREM Spec => RelayLtl
THEOREM Spec => UnforgLtl

====