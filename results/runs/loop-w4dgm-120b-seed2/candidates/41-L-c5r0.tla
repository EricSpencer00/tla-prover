---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,       \* the set of processes in the system
    d0,         \* the default timeout interval
    SendPoint,  \* the local-clock interval at which a process sends alive messages
    PredictPoint, \* the local-clock interval at which a process predicts crashes
    Messages    \* the set of possible alive messages (one per destination)

VARIABLES
    suspect,    \* suspect[p]: the set of processes p currently suspects as crashed
    timeout,    \* timeout[p][q]: adaptive timeout interval p uses for q
    lastHeard,  \* lastHeard[p][q]: clock ticks since p last heard from q
    clock,      \* clock[p]: local clock value for process p
    outbox      \* outbox[p]: alive messages p wants to send in this transition

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ \A p \in Proc : suspect[p] \subseteq Proc
    /\ \A p \in Proc : clock[p] \in Nat
    /\ \A p \in Proc, q \in Proc : timeout[p][q] \in Nat /\ lastHeard[p][q] \in Nat

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* A process sends alive messages to everyone it suspects nothing about, at its send interval.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m # p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q \in suspect[p] THEN @ ELSE @ + 1]]
    /\ UNCHANGED <<suspect, timeout>>

\* A process predicts a crash for any process it has not heard from within its timeout.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup
                        {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> @ + 1]]
    /\ UNCHANGED <<timeout, outbox>>

\* A process receives incoming messages, clearing suspicion and adapting timeouts.
Receive(p, msgs) ==
    /\ msgs # {}
    /\ clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \ {q \in msgs : q \in suspect[p]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q \in msgs THEN 0 ELSE @]]
    /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |->
                        IF q \in msgs /\ q \in suspect[p] THEN @ + 1 ELSE @]]
    /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint * 2 /\ @ + 1 > PredictPoint * 2 /\ @ + 1 > d0 * 2
                                        THEN 0 ELSE @ + 1]
    /\ outbox' = [outbox EXCEPT ![p] = {}]

\* A process whose local clock has no action to take simply ticks along.
Tick(p) ==
    /\ clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0
    /\ ~(\E msgs \in SUBSET Proc : msgs # {} /\ msgs \subseteq Proc) \/ (\A msgs \in SUBSET Proc : msgs # {} -> msgs = {})
    /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint * 2 /\ @ + 1 > PredictPoint * 2 /\ @ + 1 > d0 * 2 THEN 0 ELSE @ + 1]
    /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc, msgs \in SUBSET Proc : Receive(p, msgs)
    \/ \E p \in Proc : Tick(p)

Spec == Init /\ [][Next]_vars

====