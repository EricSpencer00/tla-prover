---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\*-----------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------
CONSTANT N, T, F

\*-----------------------------------------------------------------
\* Derived sets
\*-----------------------------------------------------------------
Proc == 1..N

\*-----------------------------------------------------------------
\* Variables
\*-----------------------------------------------------------------
VARIABLES Correct, Faulty, InitRecv, EchoRecv, EchoSent, Accepted

vars == <<Correct, Faulty, InitRecv, EchoRecv, EchoSent, Accepted>>

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
EchoCount(p) == Cardinality(EchoRecv[p])

\* InitAllBroadcast is now a state function that takes the set of correct
\* processes as an argument, avoiding a direct reference to the variable
\* Correct in its definition.
InitAllBroadcast(C) == InitRecv = C
NoBroadcast       == InitRecv = {}

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ InitRecv \subseteq Correct
  /\ EchoRecv = [p \in Proc |-> {}]
  /\ EchoSent = [p \in Proc |-> FALSE]
  /\ Accepted = {}

\*-----------------------------------------------------------------
\* Actions
\*-----------------------------------------------------------------
\* (1) Receive new ECHO messages (from any sender, correct or Byzantine)
Receive(p) ==
  /\ p \in Correct
  /\ \E newRecv \in SUBSET ((Correct \cup Faulty) \ EchoRecv[p]) :
        /\ EchoRecv' = [EchoRecv EXCEPT ![p] = EchoRecv[p] \cup newRecv]
        /\ UNCHANGED <<Correct, Faulty, InitRecv, EchoSent, Accepted>>

\* (2) Process that initially received the broadcaster's INIT
InitAct(p) ==
  /\ p \in Correct
  /\ p \in InitRecv
  /\ EchoSent' = [EchoSent EXCEPT ![p] = TRUE]
  /\ Accepted' = Accepted \cup {p}
  /\ UNCHANGED <<Correct, Faulty, InitRecv, EchoRecv>>

\* (3) Not yet sent ECHO, received enough (>= N-2T) but < N-T : send ECHO only
Cond1(p) ==
  /\ p \in Correct
  /\ ~EchoSent[p]
  /\ EchoCount(p) >= N - 2 * T
  /\ EchoCount(p) <  N - T
  /\ EchoSent' = [EchoSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<Correct, Faulty, InitRecv, EchoRecv, Accepted>>

\* (4) Not yet sent ECHO, received >= N-T : send ECHO and accept
Cond2(p) ==
  /\ p \in Correct
  /\ ~EchoSent[p]
  /\ EchoCount(p) >= N - T
  /\ EchoSent' = [EchoSent EXCEPT ![p] = TRUE]
  /\ Accepted' = Accepted \cup {p}
  /\ UNCHANGED <<Correct, Faulty, InitRecv, EchoRecv>>

\* (5) Already sent ECHO, received >= N-T : accept
Cond3(p) ==
  /\ p \in Correct
  /\ EchoSent[p]
  /\ p \notin Accepted
  /\ EchoCount(p) >= N - T
  /\ Accepted' = Accepted \cup {p}
  /\ UNCHANGED <<Correct, Faulty, InitRecv, EchoRecv, EchoSent>>

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : InitAct(p)
  \/ \E p \in Correct : Cond1(p)
  \/ \E p \in Correct : Cond2(p)
  \/ \E p \in Correct : Cond3(p)

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ InitRecv \subseteq Correct
  /\ EchoRecv \in [Proc -> SUBSET Proc]
  /\ \A p \in Proc : EchoRecv[p] \subseteq Proc
  /\ EchoSent \in [Proc -> BOOLEAN]
  /\ Accepted \subseteq Correct
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F

\*-----------------------------------------------------------------
\* Temporal properties
\*-----------------------------------------------------------------
CorrLtl == [] (InitAllBroadcast(Correct) => <> (Accepted = Correct))

RelayLtl == [] ( (\E p \in Correct : p \in Accepted) => <> (Accepted = Correct) )

UnforgLtl == [] (NoBroadcast => [] (Accepted = {}))

====