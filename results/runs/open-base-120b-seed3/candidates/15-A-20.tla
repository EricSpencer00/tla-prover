---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* -------------------------------------------------
\* Process set
\* -------------------------------------------------
PROC == 1..N

\* -------------------------------------------------
\* Variables
\* -------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, EchoSent

vars == <<Correct, Faulty, pc, recv, EchoSent>>

\* -------------------------------------------------
\* Helper constants
\* -------------------------------------------------
NMinus2T == N - 2 * T
NMinusT  == N - T

\* -------------------------------------------------
\* Type correctness
\* -------------------------------------------------
TypeOK ==
    /\ Correct \subseteq PROC
    /\ Faulty = PROC \ Correct
    /\ Cardinality(Correct) = N - F
    /\ pc \in [PROC -> {"NoInit", "Init", "Echo", "Accept"}]
    /\ recv \in [PROC -> SUBSET PROC]
    /\ EchoSent \subseteq Correct

\* -------------------------------------------------
\* Fault‑configuration constraints
\* -------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ Correct \subseteq PROC
    /\ Faulty = PROC \ Correct
    /\ Cardinality(Correct) = N - F
    /\ EchoSent = {}
    /\ recv = [p \in PROC |-> {}]
    /\ pc = [p \in PROC |-> 
            IF p \in Correct
                THEN IF RandomChoice({"Init","NoInit"}) = "Init"
                        THEN "Init"
                        ELSE "NoInit"
                ELSE "NoInit"
          ]

\* -------------------------------------------------
\* Receive action (a correct process may receive any subset
\* of messages that could have been sent by correct processes
\* (those in EchoSent) or by Byzantine processes (any faulty))
\* -------------------------------------------------
Receive(p) ==
    /\ p \in Correct
    /\ newRecv \in SUBSET ((EchoSent \cup Faulty) \ recv[p])
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newRecv]
    /\ UNCHANGED <<Correct, Faulty, pc, EchoSent>>

\* -------------------------------------------------
\* Send ECHO and accept immediately (process started with INIT)
\* -------------------------------------------------
SendInitAccept(p) ==
    /\ p \in Correct
    /\ pc[p] = "Init"
    /\ EchoSent' = EchoSent \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED <<Correct, Faulty, recv>>

\* -------------------------------------------------
\* Send ECHO only (enough ECHO messages but not enough to accept)
\* -------------------------------------------------
SendEcho(p) ==
    /\ p \in Correct
    /\ pc[p] = "NoInit"
    /\ Cardinality(recv[p]) >= NMinus2T
    /\ Cardinality(recv[p]) < NMinusT
    /\ EchoSent' = EchoSent \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "Echo"]
    /\ UNCHANGED <<Correct, Faulty, recv>>

\* -------------------------------------------------
\* Send ECHO and accept (enough ECHO messages)
\* -------------------------------------------------
SendEchoAccept(p) ==
    /\ p \in Correct
    /\ pc[p] \in {"NoInit", "Init"}
    /\ Cardinality(recv[p]) >= NMinusT
    /\ EchoSent' = EchoSent \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED <<Correct, Faulty, recv>>

\* -------------------------------------------------
\* Accept after having already sent ECHO
\* -------------------------------------------------
Accept(p) ==
    /\ p \in Correct
    /\ pc[p] = "Echo"
    /\ Cardinality(recv[p]) >= NMinusT
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED <<Correct, Faulty, recv, EchoSent>>

\* -------------------------------------------------
\* Overall next‑state relation
\* -------------------------------------------------
Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : SendInitAccept(p)
    \/ \E p \in Correct : SendEcho(p)
    \/ \E p \in Correct : SendEchoAccept(p)
    \/ \E p \in Correct : Accept(p)

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* -------------------------------------------------
\* Invariants
\* -------------------------------------------------
INVARS == TypeOK /\ FCConstraints

\* -------------------------------------------------
\* LTL properties
\* -------------------------------------------------
CorrLtl ==
    [] ( ( \A p \in Correct : pc[p] = "Init")
          => <> ( \A p \in Correct : pc[p] = "Accept") )

RelayLtl ==
    [] ( ( \E p \in Correct : pc[p] = "Accept")
          => <> ( \A p \in Correct : pc[p] = "Accept") )

UnforgLtl ==
    [] ( ( \A p \in Correct : pc[p] = "NoInit")
          => [] ( \A p \in Correct : pc[p] # "Accept") )

\* -------------------------------------------------
\* Exported identifiers (as required by the .cfg file)
\* -------------------------------------------------
CONSTANT N, T, F
SPECIFICATION Spec
INVARIANTS TypeOK, FCConstraints
PROPERTIES CorrLtl, RelayLtl, UnforgLtl

====