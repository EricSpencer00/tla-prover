---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process universe
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Message definition (only ECHO messages)
\* ----------------------------------------------------------------------
AllEchos == { <<p, "ECHO">> : p \in Proc }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, Sent

vars == <<Correct, Faulty, pc, recv, Sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p) == { m[1] : m \in recv[p] /\ m[2] = "ECHO" }

SentEcho(p) == <<p, "ECHO">> \in Sent

NMinus2T == N - 2 * T
NMinusT  == N - T

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    LET InitSet == CHOOSE S \subseteq Correct : TRUE IN
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc = [p \in Proc |-> IF p \in InitSet THEN "Init" ELSE "NoInit"]
    /\ Sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Receive arbitrary new ECHO messages (including Byzantine ones)
Receive(p, new) ==
    /\ p \in Correct
    /\ new \subseteq AllEchos \ recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
    /\ UNCHANGED <<Sent, pc, Correct, Faulty>>

\* 2. Process that started with INIT sends ECHO and accepts immediately
InitAction(p) ==
    /\ pc[p] = "Init"
    /\ Sent' = Sent \cup {<<p, "ECHO">>}
    /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED recv

\* 3. Process that has not sent ECHO yet, receives >= N-2T but < N-T ECHOs
Thresh1Action(p) ==
    /\ pc[p] = "NoInit"
    /\ ~SentEcho(p)
    /\ Cardinality(EchoSenders(p)) >= NMinus2T
    /\ Cardinality(EchoSenders(p)) <  NMinusT
    /\ Sent' = Sent \cup {<<p, "ECHO">>}
    /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
    /\ UNCHANGED recv

\* 4. Process that has not sent ECHO yet, receives >= N-T ECHOs
Thresh2Action(p) ==
    /\ pc[p] = "NoInit"
    /\ ~SentEcho(p)
    /\ Cardinality(EchoSenders(p)) >= NMinusT
    /\ Sent' = Sent \cup {<<p, "ECHO">>}
    /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED recv

\* 5. Process that already sent ECHO, now receives >= N-T ECHOs and accepts
AcceptAfterSend(p) ==
    /\ SentEcho(p)
    /\ pc[p] # "Accepted"
    /\ Cardinality(EchoSenders(p)) >= NMinusT
    /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<recv, Sent>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Correct :
          \E new \subseteq AllEchos \ recv[p] :
                Receive(p, new)
    \/ \E p \in Correct : InitAction(p)
    \/ \E p \in Correct : Thresh1Action(p)
    \/ \E p \in Correct : Thresh2Action(p)
    \/ \E p \in Correct : AcceptAfterSend(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"Init", "NoInit", "EchoSent", "Accepted"}]
    /\ recv \in [Proc -> SUBSET AllEchos]
    /\ Sent \subseteq AllEchos

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL Properties
\* ----------------------------------------------------------------------
AllInit   == \A p \in Correct : pc[p] = "Init"
AllNoInit == \A p \in Correct : pc[p] = "NoInit"
AllAccept == \A p \in Correct : pc[p] = "Accepted"

CorrLtl  == [] ( AllInit => <> AllAccept )
RelayLtl == [] ( (\E p \in Correct : pc[p] = "Accepted") => <> AllAccept )
UnforgLtl == [] ( AllNoInit => [] ( \A p \in Correct : pc[p] # "Accepted" ) )

====