---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, T, F

VARIABLES Correct, Faulty, pc, recv, sent

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Proc == 1 .. N

Msg == Proc \X {"ECHO"}

Senders(s) == { m[1] : m \in s }

CountEcho(p) == Cardinality(Senders(recv[p]))

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Proc = 1..N
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"NoInit", "InitRecv", "EchoSent", "Accepted"}]
    /\ recv \in [Proc -> SUBSET Msg]
    /\ sent \in SUBSET Msg
    /\ \A p \in Correct :
          (pc[p] = "Accepted"  => <<p, "ECHO">> \in sent)
    /\ \A p \in Correct :
          (pc[p] = "EchoSent" => <<p, "ECHO">> \in sent)

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
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ sent = {}
    /\ \A p \in Proc : recv[p] = {}
    /\ \A p \in Proc : pc[p] \in {"NoInit", "InitRecv"}
    /\ TypeOK
    /\ FCConstraints

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Correct process receives new messages (from correct senders or any Byzantine)
Receive(p) ==
    /\ p \in Correct
    LET possible == sent \cup { <<q, "ECHO">> : q \in Faulty } IN
    \E new \in SUBSET possible :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

\* 2. Process that already has INIT immediately sends ECHO and accepts
ActionInit(p) ==
    /\ p \in Correct
    /\ pc[p] = "InitRecv"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { <<p, "ECHO">> }
    /\ UNCHANGED <<Correct, Faulty, recv>>

\* 3. Process without ECHO yet receives enough (N-2T) but not enough (N-T) to accept
ActionEchoNoAccept(p) ==
    /\ p \in Correct
    /\ pc[p] = "NoInit"
    /\ CountEcho(p) >= N - 2 * T
    /\ CountEcho(p) <  N - T
    /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
    /\ sent' = sent \cup { <<p, "ECHO">> }
    /\ UNCHANGED <<Correct, Faulty, recv>>

\* 4. Process sends (if not already) and accepts when it has ≥ N‑T ECHO messages
ActionEchoAccept(p) ==
    /\ p \in Correct
    /\ \/ (pc[p] = "NoInit"  /\ CountEcho(p) >= N - T)
       \/ (pc[p] = "EchoSent" /\ CountEcho(p) >= N - T)
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = IF <<p, "ECHO">> \in sent
               THEN sent
               ELSE sent \cup { <<p, "ECHO">> }
    /\ UNCHANGED <<Correct, Faulty, recv>>

Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : ActionInit(p)
    \/ \E p \in Correct : ActionEchoNoAccept(p)
    \/ \E p \in Correct : ActionEchoAccept(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Correct, Faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Temporal properties
\* ----------------------------------------------------------------------
CorrLtl ==
    [] ( (\A p \in Correct : pc[p] = "InitRecv")
        => <> (\A p \in Correct : pc[p] = "Accepted") )

RelayLtl ==
    [] ( (\E p \in Correct : pc[p] = "Accepted")
        => <> (\A p \in Correct : pc[p] = "Accepted") )

UnforgLtl ==
    [] ( (\A p \in Correct : pc[p] = "NoInit")
        => [] (\A p \in Correct : pc[p] # "Accepted") )

\* ----------------------------------------------------------------------
\* Theorems (optional, for model checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====