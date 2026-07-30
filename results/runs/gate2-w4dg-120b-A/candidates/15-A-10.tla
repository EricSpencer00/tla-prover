---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Roles == {"none", "init", "echo", "accept"}
MessageTypes == {"ECHO"}
Senders == 0..(N - 1)

MaxCount == Cardinality(Senders)

VARIABLES correct, faulty, role, recvd, sent

vars == <<correct, faulty, role, recvd, sent>>

TypeOK ==
    /\ correct \subseteq Senders
    /\ Cardinality(correct) = N - F
    /\ faulty = Senders \ correct
    /\ role \in [Senders -> Roles]
    /\ recvd \in [Senders -> SUBSET (Senders \X MessageTypes)]
    /\ sent \in SUBSET (Senders \X MessageTypes)

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* A restricted initial state for checking the no-broadcast case: no correct
\* process starts in the broadcast-received state.
InitA0 ==
    /\ correct = {0..(N - 1)}
    /\ faulty = {}
    /\ role = [p \in Senders |-> "none"]
    /\ recvd = [p \in Senders |-> {}]
    /\ sent = {}

Init0 == InitA0 /\ correct = {0..(N - 1)} /\ faulty = {}

Init ==
    \/ Init0
    \/ /\ correct = {0..(N - 1)} \ {0}
       /\ faulty = {0}
       /\ \E r \in [Senders -> Roles] :
            /\ r[0] = "init"
            /\ \A p \in Senders \ {0} : r[p] = "none"
            /\ role' = r
       /\ recvd' = [p \in Senders |-> {}]
       /\ sent' = {}
       /\ UNCHANGED <<correct, faulty>>

\* A correct process may receive a set of messages from correct and faulty
\* senders at once, which is what lets it accumulate the quorum it needs.
ReceiveCorrect(p) ==
    /\ role[p] \in {"none", "init"}
    /\ \E S \subseteq (([Senders \X MessageTypes] \ sent) \cup (faulty \X MessageTypes)) :
         /\ S # {}
         /\ recvd' = [recvd EXCEPT ![p] = @ \cup S]
    /\ UNCHANGED <<correct, faulty, role, sent>>

\* The broadcaster's INIT message is implicit: a process that started in the
\* broadcast-received state may accept and send ECHO immediately, with no
\* quorum check at all.
InitReceivedAct(p) ==
    /\ role[p] = "init"
    /\ role' = [role EXCEPT ![p] = "accept"]
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, recvd>>

SendEcho(p) ==
    /\ role[p] = "none"
    /\ Cardinality({q \in Senders : <<q, "ECHO">> \in recvd[p]}) >= N - 2 * T
    /\ Cardinality({q \in Senders : <<q, "ECHO">> \in recvd[p]}) < N - T
    /\ role' = [role EXCEPT ![p] = "echo"]
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, recvd>>

AcceptLater(p) ==
    /\ role[p] = "none"
    /\ Cardinality({q \in Senders : <<q, "ECHO">> \in recvd[p]}) >= N - T
    /\ role' = [role EXCEPT ![p] = "accept"]
    /\ sent' = sent \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, recvd>>

AcceptOnEcho(p) ==
    /\ role[p] = "echo"
    /\ Cardinality({q \in Senders : <<q, "ECHO">> \in recvd[p]}) >= N - T
    /\ role' = [role EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<correct, faulty, recvd, sent>>

\* Weak fairness below: every correct process's combined receive-and-act step
\* must eventually happen if it can forever take steps against correct senders.
ReceiveAny ==
    /\ \E p \in correct : ReceiveCorrect(p) \/ InitReceivedAct(p) \/ SendEcho(p) \/ AcceptLater(p) \/ AcceptOnEcho(p)
    /\ UNCHANGED vars

Next ==
    \/ ReceiveAny
    \/ \E p \in correct : InitReceivedAct(p)
    \/ \E p \in correct : SendEcho(p)
    \/ \E p \in correct : AcceptLater(p)
    \/ \E p \in correct : AcceptOnEcho(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ReceiveAny)

UnforgLtl == (\A p \in correct : role[p] = "none") ~> (\A p \in correct : role[p] = "none")
CorrLtl == (\A p \in correct : role[p] = "init") ~> (\A p \in correct : role[p] = "accept")
RelayLtl == (\E p \in correct : role[p] = "accept") ~> (\A p \in correct : role[p] = "accept")

====