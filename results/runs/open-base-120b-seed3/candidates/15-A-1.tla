---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F

\* -----------------------------------------------------------------
\* Process set
\* -----------------------------------------------------------------
Proc == 1 .. N

\* -----------------------------------------------------------------
\* Message definition (only ECHO messages)
\* -----------------------------------------------------------------
ECHO == "ECHO"
EchoMsg(p) == <<p, ECHO>>

\* -----------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

vars == <<Correct, Faulty, pc, sent, recv>>

\* -----------------------------------------------------------------
\* Helper functions
\* -----------------------------------------------------------------
EchoSenders(p) == { s \in Proc : EchoMsg(s) \in recv[p] }

EchoCount(p) == Cardinality(EchoSenders(p))

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \\ Correct
  /\ pc \in [Proc -> {"InitRecvd", "StartNoInit", "EchoSent", "Accepted"}]
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ \A p \in Proc :
        \/ pc[p] = "InitRecvd"
        \/ pc[p] = "StartNoInit"

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
\* (1) Receive a non‑deterministic set of new messages
Receive(p) ==
  /\ p \in Correct
  /\ LET possible == sent \cup { EchoMsg(q) : q \in Faulty } IN
     \E new \in SUBSET(possible) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

\* (2) Process that already has the INIT message accepts and sends ECHO
InitAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "InitRecvd"
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

\* (3) Receive enough ECHOs (N-2T ≤ count < N-T) and send ECHO (no accept yet)
SendEchoOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "StartNoInit"
  /\ N - 2*T <= EchoCount(p)
  /\ EchoCount(p) < N - T
  /\ sent' = sent \cup { EchoMsg(p) }
  /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

\* (4) Receive at least N‑T ECHOs, send ECHO if not yet sent, and accept
AcceptAndEcho(p) ==
  /\ p \in Correct
  /\ EchoCount(p) >= N - T
  /\ \/ pc[p] = "StartNoInit"
     \/ pc[p] = "EchoSent"
  /\ sent' = IF pc[p] = "StartNoInit" THEN sent \cup { EchoMsg(p) } ELSE sent
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

\* (5) Already sent ECHO, now enough ECHOs to accept
AcceptOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ EchoCount(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, sent, recv>>

\* -----------------------------------------------------------------
\* Combined next‑state relation
\* -----------------------------------------------------------------
Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : InitAccept(p)
  \/ \E p \in Correct : SendEchoOnly(p)
  \/ \E p \in Correct : AcceptAndEcho(p)
  \/ \E p \in Correct : AcceptOnly(p)

\* -----------------------------------------------------------------
\* Fairness (weak fairness on the receive step)
\* -----------------------------------------------------------------
RecvAct == \/ \E p \in Correct : Receive(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(RecvAct)

\* -----------------------------------------------------------------
\* Type safety invariant
\* -----------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \\ Correct
  /\ pc \in [Proc -> {"InitRecvd", "StartNoInit", "EchoSent", "Accepted"}]
  /\ sent \subseteq { EchoMsg(p) : p \in Correct }
  /\ \A p \in Proc : recv[p] \subseteq { EchoMsg(q) : q \in Proc }

\* -----------------------------------------------------------------
\* Fault‑constraint invariant (bounds on parameters)
\* -----------------------------------------------------------------
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* -----------------------------------------------------------------
\* LTL properties
\* -----------------------------------------------------------------
\* All correct processes start with the INIT message
InitAll == \A p \in Correct : pc[p] = "InitRecvd"

\* All correct processes have accepted
AllAccepted == \A p \in Correct : pc[p] = "Accepted"

\* At least one correct process has accepted
ExistsAccepted == \E p \in Correct : pc[p] = "Accepted"

\* No correct process received the INIT message initially
InitNoBroadcast == \A p \in Correct : pc[p] = "StartNoInit"

CorrLtl == [] ( InitAll => <> AllAccepted )

RelayLtl == [] ( ExistsAccepted => <> AllAccepted )

UnforgLtl == [] ( InitNoBroadcast => [] ( \A p \in Correct : pc[p] # "Accepted") )

\* -----------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* -----------------------------------------------------------------
INVARIANTS == TypeOK, FCConstraints
PROPERTIES == CorrLtl, RelayLtl, UnforgLtl

====