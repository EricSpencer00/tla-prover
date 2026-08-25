---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Message definition (only ECHO type)
\* ----------------------------------------------------------------------
ECHOMsg(s) == [type |-> "ECHO", from |-> s]

Msg == UNION {ECHOMsg(p) : p \in Proc}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, sent

vars == <<Correct, Faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p, rcvSet) == { s \in Proc : ECHOMsg(s) \in rcvSet }

CntEcho(p, rcvSet) == Cardinality(EchoSenders(p, rcvSet))

NewPc(p, rcvSet, oldPc) ==
  IF oldPc = "InitYes" THEN
    "Accepted"
  ELSE IF oldPc = "InitNo" THEN
    LET cnt == CntEcho(p, rcvSet) IN
      IF cnt >= N - T THEN
        "Accepted"
      ELSE IF cnt >= N - 2 * T THEN
        "EchoSent"
      ELSE
        "InitNo"
  ELSE IF oldPc = "EchoSent" THEN
    LET cnt == CntEcho(p, rcvSet) IN
      IF cnt >= N - T THEN
        "Accepted"
      ELSE
        "EchoSent"
  ELSE
    "Accepted"

SentUpdate(p, oldPc, newPc, sentSet) ==
  IF (oldPc # "EchoSent" /\ oldPc # "Accepted") /\ (newPc = "EchoSent" \/ newPc = "Accepted")
    THEN sentSet \cup {ECHOMsg(p)}
    ELSE sentSet

\* ----------------------------------------------------------------------
\* Initialization (nondeterministic choice of the set of correct processes)
\* ----------------------------------------------------------------------
Init ==
  \E CorrectSet \in SUBSET Proc :
    /\ Cardinality(CorrectSet) = N - F
    /\ Correct = CorrectSet
    /\ Faulty = Proc \ CorrectSet
    /\ pc \in [Proc -> {"InitNo", "InitYes", "EchoSent", "Accepted"}]
    /\ \A p \in CorrectSet : pc[p] \in {"InitNo", "InitYes"}
    /\ recv = [p \in Proc |-> {}]
    /\ sent = {}

\* ----------------------------------------------------------------------
\* One-step action for a correct process
\* ----------------------------------------------------------------------
RecAct(p) ==
  /\ p \in Correct
  /\ \E newMsgs \in SUBSET( sent \cup {ECHOMsg(b) : b \in Faulty} ) :
       LET rcvNew == recv[p] \cup newMsgs IN
       LET newPc  == NewPc(p, rcvNew, pc[p]) IN
         /\ recv' = [recv EXCEPT ![p] = rcvNew]
         /\ pc'   = [pc   EXCEPT ![p] = newPc]
         /\ sent' = SentUpdate(p, pc[p], newPc, sent)
         /\ UNCHANGED <<Correct, Faulty>>

Next ==
  \E p \in Correct : RecAct(p)

\* ----------------------------------------------------------------------
\* Fairness (weak fairness on each correct process's action)
\* ----------------------------------------------------------------------
Fairness ==
  \A p \in Proc : WF_vars(RecAct(p))

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ Fairness

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"InitNo","InitYes","EchoSent","Accepted"}]
  /\ recv \in [Proc -> SUBSET(Msg)]
  /\ sent \subseteq Msg
  /\ \A m \in sent : m.type = "ECHO" /\ m.from \in Proc

FCConstraints ==
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* Temporal properties
\* ----------------------------------------------------------------------
CorrLtl == ( \A p \in Correct : pc[p] = "InitYes" )
           => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl == ( \E p \in Correct : pc[p] = "Accepted" )
            => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl == ( \A p \in Correct : pc[p] = "InitNo" )
             => [] ( \A p \in Correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* The required identifiers for the configuration file
\* ----------------------------------------------------------------------
\* CONSTANTS: N, T, F are declared above
\* SPECIFICATION: Spec
\* INVARIANTS: TypeOK, FCConstraints
\* PROPERTIES: CorrLtl, RelayLtl, UnforgLtl

====