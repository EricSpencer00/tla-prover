---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

VARIABLES
    suspect,
    timeout,
    elapsed,
    clock,
    pending

vars == <<suspect, timeout, elapsed, clock, pending>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ elapsed \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ pending \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ elapsed = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ pending = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ pending' = [pending EXCEPT ![p] = {m \in Messages : m.receiver = q \in Proc \ {p}}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ elapsed' = [elapsed EXCEPT ![q] = IF elapsed[q] < timeout[q] THEN elapsed[q] + 1 ELSE elapsed[q] : q \in Proc]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in Proc \ {p} : elapsed[q] > timeout[q]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ elapsed' = [elapsed EXCEPT ![q] = IF elapsed[q] < timeout[q] THEN elapsed[q] + 1 ELSE elapsed[q] : q \in Proc]
    /\ UNCHANGED <<timeout, pending>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E s \in [q \in Proc \ {p}, r \in {FALSE, TRUE}] :
        /\ elapsed' = [elapsed EXCEPT ![s.q] = 0]
        /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {s.q}]
        /\ timeout' = [timeout EXCEPT ![s.q] = IF s.r THEN timeout[s.q] + 1 ELSE timeout[s.q]]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > timeout[s.q] /\ clock[p] + 1 > PredictPoint /\ clock[p] + 1 > SendPoint THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED pending

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====