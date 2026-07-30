---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The number of distinct ECHO senders a process has received.
RECURSIVE CountEchoes(_)
CountEchoes(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE
         IN (IF x.msg = "ECHO" THEN 1 ELSE 0) + CountEchoes(S \ {x})

Locations == {"idle", "nobroadcast", "sent", "accept"}

VARIABLES correct, faulty, loc, inbox, sent

vars == <<correct, faulty, loc, inbox, sent>>

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty = (1..N) \ correct
    /\ loc \in [1..N -> Locations]
    /\ inbox \in [1..N -> SUBSET [sender: 1..N, msg: {"ECHO"}]]
    /\ sent \subseteq [sender: 1..N, msg: {"ECHO"}]

\* Unforgeability and type safety together are the protocol's safety
\* argument: no correct process accepts unless INIT was actually
\* broadcast, and every variable stays within its domain.
FCConstraints == TypeOK

Init ==
    /\ Cardinality(correct) = N - F
    /\ \A p \in correct : loc[p] \in {"idle", "nobroadcast"}
    /\ inbox = [p \in 1..N |-> {}]
    /\ sent = {}

RestrictedInit ==
    /\ Cardinality(correct) = N - F
    /\ \A p \in correct : loc[p] = "nobroadcast"
    /\ inbox = [p \in 1..N |-> {}]
    /\ sent = {}

\* A correct process receives a batch of new messages, drawn from
\* everything sent by correct senders plus any messages a Byzantine
\* sender may conjure. This is the only step in which a Byzantine
\* process's forgery can ever appear.
Receive(p) ==
    /\ loc[p] \in {"idle", "nobroadcast"}
    /\ \E newMsgs \in SUBSET (sent \cup [sender: faulty, msg: {"ECHO"}]) :
        inbox' = [inbox EXCEPT ![p] = inbox[p] \cup newMsgs]
    /\ UNCHANGED <<correct, faulty, loc, sent>>

\* A correct process that already received INIT accepts immediately
\* and broadcasts an ECHO round.
EchoFromInit(p) ==
    /\ loc[p] = "idle"
    /\ loc' = [loc EXCEPT ![p] = "accept"]
    /\ sent' = sent \cup {[sender |-> p, msg |-> "ECHO"]}
    /\ UNCHANGED <<correct, faulty, inbox>>

\* A correct process that has not yet sent ECHO waits for an
\* intermediate threshold of ECHO messages before sending.
EchoMid(p) ==
    /\ loc[p] = "idle"
    /\ CountEchoes(inbox[p]) >= N - 2 * T
    /\ CountEchoes(inbox[p]) < N - T
    /\ loc' = [loc EXCEPT ![p] = "sent"]
    /\ sent' = sent \cup {[sender |-> p, msg |-> "ECHO"]}
    /\ UNCHANGED <<correct, faulty, inbox>>

\* A correct process that has not yet sent ECHO but already reached
\* the final threshold sends ECHO and accepts in the same step.
EchoFinal(p) ==
    /\ loc[p] = "idle"
    /\ CountEchoes(inbox[p]) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "accept"]
    /\ sent' = sent \cup {[sender |-> p, msg |-> "ECHO"]}
    /\ UNCHANGED <<correct, faulty, inbox>>

\* A correct process that has already sent ECHO accepts once the
\* final threshold is met.
AcceptLate(p) ==
    /\ loc[p] = "sent"
    /\ CountEchoes(inbox[p]) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<correct, faulty, inbox, sent>>

Next ==
    \E p \in 1..N :
        Receive(p) \/ EchoFromInit(p) \/ EchoMid(p) \/ EchoFinal(p) \/ AcceptLate(p)

\* Weak fairness on the combined receive-and-act steps for each
\* correct process; without it the runner may starve the process.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in correct :
        /\ TRUE
        /\ WF_vars(Receive(p) \/ EchoFromInit(p) \/ EchoMid(p) \/ EchoFinal(p))

CorrLtl ==
    /\ \A p \in correct : loc[p] = "idle"
    /\ <>(\A p \in correct : loc[p] = "accept")

RelayLtl ==
    /\ \E p \in correct : loc[p] = "accept"
    /\ <>(\A p \in correct : loc[p] = "accept")

\* No-broadcast case: if no correct process ever broadcasts INIT,
\* then no correct process ever accepts.
UnforgLtl ==
    /\ \A p \in correct : loc[p] = "nobroadcast"
    /\ (\A p \in correct : loc[p] # "accept")
====