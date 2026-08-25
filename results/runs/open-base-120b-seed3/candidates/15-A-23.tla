---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\*  Basic sets
\* ----------------------------------------------------------------------
Proc == 1 .. N

Msg == [type : {"ECHO"}, from : Proc]

\* ----------------------------------------------------------------------
\*  Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
Senders(p) == { m.from : m \in recv[p] }

Cnt(p) == Cardinality(Senders(p))

\* ----------------------------------------------------------------------
\*  Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"NoInit", "Init", "Echoed", "Accepted"}]
    /\ sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\*  Fault‑correctness constraints (configuration constraints)
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ Cardinality(Correct) = N - F

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"NoInit", "Init", "Echoed", "Accepted"}]
    /\ \A p \in Correct : pc[p] \in {"NoInit", "Init"}
    /\ \A p \in Faulty : pc[p] = "NoInit"
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in Correct
    /\ \E new \in SUBSET Msg :
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
          /\ UNCHANGED <<Correct, Faulty, pc, sent>>

SendEchoAndAccept(p) ==
    /\ p \in Correct
    /\ pc[p] = "Init"
    /\ sent' = sent \cup {[type |-> "ECHO", from |-> p}]
    /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<Correct, Faulty, recv>>

SendEcho(p) ==
    /\ p \in Correct
    /\ pc[p] = "NoInit"
    /\ Cnt(p) >= N - 2 * T
    /\ Cnt(p) <  N - T
    /\ sent' = sent \cup {[type |-> "ECHO", from |-> p}]
    /\ pc'   = [pc EXCEPT ![p] = "Echoed"]
    /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoAndAcceptFromNoInit(p) ==
    /\ p \in Correct
    /\ pc[p] = "NoInit"
    /\ Cnt(p) >= N - T
    /\ sent' = sent \cup {[type |-> "ECHO", from |-> p}]
    /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<Correct, Faulty, recv>>

Accept(p) ==
    /\ p \in Correct
    /\ pc[p] = "Echoed"
    /\ Cnt(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<Correct, Faulty, sent, recv>>

ProcStep(p) ==
    \/ Receive(p)
    \/ SendEchoAndAccept(p)
    \/ SendEcho(p)
    \/ SendEchoAndAcceptFromNoInit(p)
    \/ Accept(p)

Next ==
    \E p \in Correct : ProcStep(p)

vars == <<Correct, Faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*  LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
    [] ( ( \A p \in Correct : pc[p] = "Init" )
        => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

RelayLtl ==
    [] ( ( \E p \in Correct : pc[p] = "Accepted" )
        => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

UnforgLtl ==
    [] ( ( \A p \in Correct : pc[p] = "NoInit" )
        => [] ( \A p \in Correct : pc[p] # "Accepted" ) )

\* ----------------------------------------------------------------------
\*  Theorems (optional, for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====