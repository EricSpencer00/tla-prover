---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES Correct, Faulty, pc, recv, sent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Message == [type : {"ECHO"}, from : 1..N]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ByzMsgs == { [type |-> "ECHO", from |-> f] : f \in Faulty }

CountEcho(p) ==
  Cardinality({ m.from : m \in recv[p] /\ m.type = "ECHO" })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ \E C \in SUBSET 1..N :
        /\ Cardinality(C) = N - F
        /\ Correct = C
        /\ Faulty = 1..N \ C
  /\ pc \in [1..N -> {"Init", "NoInit"}]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ \E new \in SUBSET (sent \cup ByzMsgs) :
        /\ new \subseteq (sent \cup ByzMsgs) \ recv[p]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

InitAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ UNCHANGED <<Correct, Faulty, recv>>

EchoSend(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ CountEcho(p) >= N - 2*T
  /\ CountEcho(p) <  N - T
  /\ pc' = [pc EXCEPT ![p] = "Echo"]
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ UNCHANGED <<Correct, Faulty, recv>>

EchoSendAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ CountEcho(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptAfterEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "Echo"
  /\ CountEcho(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, recv, sent>>

Stutter ==
  UNCHANGED <<Correct, Faulty, pc, recv, sent>>

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : InitAccept(p)
  \/ \E p \in Correct : EchoSend(p)
  \/ \E p \in Correct : EchoSendAccept(p)
  \/ \E p \in Correct : AcceptAfterEcho(p)
  \/ Stutter

vars == <<Correct, Faulty, pc, recv, sent>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq 1..N
  /\ Faulty = 1..N \ Correct
  /\ pc \in [1..N -> {"Init","NoInit","Echo","Accept"}]
  /\ recv \in [1..N -> SUBSET Message]
  /\ sent \in SUBSET Message

FCConstraints ==
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
AllInit == \A p \in Correct : pc[p] = "Init"
AllAccept == \A p \in Correct : pc[p] = "Accept"
AnyAccept == \E p \in Correct : pc[p] = "Accept"
NoInit == \A p \in Correct : pc[p] # "Init"
NoAccept == \A p \in Correct : pc[p] # "Accept"

CorrLtl == [] ( AllInit => <> AllAccept )
RelayLtl == [] ( AnyAccept => <> AllAccept )
UnforgLtl == [] ( NoInit => NoAccept )

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* CONSTANTS: N, T, F   (declared above)
\* SPECIFICATION: Spec
\* INVARIANTS: TypeOK, FCConstraints
\* PROPERTIES: CorrLtl, RelayLtl, UnforgLtl

====