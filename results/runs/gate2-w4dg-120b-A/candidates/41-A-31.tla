---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,          \* the set of processes
    d0,            \* default timeout interval
    SendPoint,     \* clock value (modulus) when a process sends alive messages
    PredictPoint,  \* clock value (modulus) when a process predicts failures
    Messages       \* the set of possible message contents (e.g. alive)

VARIABLES
    suspect,       \* [Proc -> SUBSET Proc] processes each process currently suspects
    interval,      \* [Proc -> [Proc -> Nat]] adaptive timeout interval each process grants every other
    lastHeard,     \* [Proc -> [Proc -> Nat]] ticks since each process last heard from each other process
    clock,         \* [Proc -> Nat] local clock value per process
    outbox         \* [Proc -> SUBSET Messages] outgoing messages a process has prepared

vars == <<suspect, interval, lastHeard, clock, outbox>>

\* Each process sends alive messages at every SendPoint tick, and predicts failures at
\* every PredictPoint tick, with the two points constrained to never coincide.
\* The modulus of the local clock is the span of all clocks plus one, since a clock
\* is reset to zero only when it exceeds every relevant threshold.

Modulus == 1 + Max({SendPoint, PredictPoint} \cup {d0} \cup {interval[p][q] : p \in Proc, q \in Proc})

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ interval = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % Modulus = SendPoint
    /\ clock[p] % Modulus # PredictPoint
    /\ outbox' = [outbox EXCEPT ![p] = Messages]
    /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % Modulus]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                       [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<suspect, interval>>

Predict(p) ==
    /\ clock[p] % Modulus = PredictPoint
    /\ clock[p] % Modulus # SendPoint
    /\ suspect' = [suspect EXCEPT ![p] =
                     @ \cup {q \in Proc : lastHeard[p][q] > interval[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % Modulus]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                       [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<interval, outbox>>

Receive(p) ==
    /\ clock[p] % Modulus # SendPoint
    /\ clock[p] % Modulus # PredictPoint
    /\ \E ms \in outbox[p] :
        /\ \E sender \in Proc :
             /\ sender \in suspect[p]
             /\ interval' = [interval EXCEPT ![p][sender] = interval[p][sender] + 1]
             /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {sender}]
             /\ lastHeard' = [lastHeard EXCEPT ![p][sender] = 0]
        /\ UNCHANGED <<suspect, interval, lastHeard>>
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % Modulus]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ interval \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

====