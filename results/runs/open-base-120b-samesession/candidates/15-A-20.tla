---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F

\* -----------------------------------------------------------------
\* Process set and message definition
\* -----------------------------------------------------------------
Proc == 1..N

EchoMsg(p) == <<p, "ECHO">>

AllMessages == { EchoMsg(p) : p \in Proc }

\* -----------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, Sent

vars == <<Correct, Faulty, pc, recv, Sent>>

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
CountEcho(p) ==
  Cardinality({ s \in Proc : EchoMsg(s) \in recv[p] })

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"Init", "NoInit", "EchoSent", "Accepted", "Byz"}]
     \* For correct processes pc is either "Init" or "NoInit"
  /\ \A p \in Correct : pc[p] \in {"Init", "NoInit"}
  /\ \A p \in Faulty : pc[p] = "Byz"
  /\ Sent = {}
  /\ \A p \in Proc : recv[p] = {}

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ LET possible == Sent \cup { EchoMsg(b) : b \in Faulty } IN
        new \in SUBSET (possible \ recv[p])
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
  /\ UNCHANGED <<Correct, Faulty, pc, Sent>>

InitAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ Sent' = Sent \cup { EchoMsg(p) }
  /\ UNCHANGED <<Correct, Faulty, recv>>

EchoNonAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ CountEcho(p) >= N - 2 * T
  /\ CountEcho(p) < N - T
  /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
  /\ Sent' = Sent \cup { EchoMsg(p) }
  /\ UNCHANGED <<Correct, Faulty, recv>>

EchoAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ CountEcho(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ Sent' = Sent \cup { EchoMsg(p) }
  /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptAfterEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ CountEcho(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv, Sent>>

Next ==
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : InitAccept(p)
  \/ \E p \in Proc : EchoNonAccept(p)
  \/ \E p \in Proc : EchoAccept(p)
  \/ \E p \in Proc : AcceptAfterEcho(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* -----------------------------------------------------------------
\* Invariants
\* -----------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"Init","NoInit","EchoSent","Accepted","Byz"}]
  /\ Sent \subseteq AllMessages
  /\ \A p \in Proc : recv[p] \subseteq AllMessages

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* -----------------------------------------------------------------
\* LTL properties
\* -----------------------------------------------------------------
AllInit == \A p \in Correct : pc[p] = "Init"
AllAccept == \A p \in Correct : pc[p] = "Accepted"
AnyAccept == \E p \in Correct : pc[p] = "Accepted"
NoInit == \A p \in Correct : pc[p] = "NoInit"

CorrLtl == [] ( AllInit => <> AllAccept )
RelayLtl == [] ( AnyAccept => <> AllAccept )
UnforgLtl == [] ( NoInit => [] ( \A p \in Correct : pc[p] # "Accepted" ) )

\* -----------------------------------------------------------------
\* Exported identifiers
\* -----------------------------------------------------------------
\* The constants N, T, F are declared above.
\* The specification is given by the operator Spec.
\* The invariants are TypeOK and FCConstraints.
\* The temporal properties are CorrLtl, RelayLtl, UnforgLtl.
====