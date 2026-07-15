---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,            \* The set of process identifiers
    d0,              \* Default timeout interval (positive integer)
    SendPoint,       \* Send interval (positive integer)
    PredictPoint,    \* Predict interval (positive integer)
    Messages         \* The set of possible message identifiers (e.g., {"alive"})

\* -----------------------------
\* Types for clarity (not constraints)
Message == [type : {"alive"}, src : Proc, dst : Proc]

\* -----------------------------
\* State variables
VARIABLES
    sus,       \* [p \in Proc -> SUBSET Proc]   : suspicion set of each process
    timeout,   \* [p \in Proc -> [q \in Proc -> Nat]] : adaptive timeout intervals
    last,      \* [p \in Proc -> [q \in Proc -> Nat]] : ticks since last alive received
    clock,     \* [p \in Proc -> Nat]                : local clock of each process
    outbox     \* [p \in Proc -> SUBSET Message]    : messages a process will send

\* -----------------------------
\* Helper definitions
AllProcsExcept(p) == Proc \ {p}
IsSend(p) == clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
IsPredict(p) == clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0

\* Reset the clock when it exceeds all thresholds
ResetClock(p) ==
    IF clock[p] > Max({SendPoint, PredictPoint} \cup {timeout[p][q] : q \in Proc})
        THEN 0
        ELSE clock[p]

\* -----------------------------
\* Initial state
Init ==
    /\ sus = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* -----------------------------
\* Actions for a single process p
SendAlive(p) ==
    /\ IsSend(p)
    /\ outbox' = [outbox EXCEPT ![p] = { [type |-> "alive", src |-> p, dst |-> r] :
                                            r \in AllProcsExcept(p) } ]
    /\ sus' = sus
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p][q] = IF q \in AllProcsExcept(p) THEN last[p][q] + 1 ELSE last[p][q] |
                 q \in Proc]
    /\ clock' = [clock EXCEPT ![p] = ResetClock(p)]

Predict(p) ==
    /\ IsPredict(p)
    /\ sus' = [sus EXCEPT ![p] = sus[p] \cup { q \in AllProcsExcept(p) :
                                            last[p][q] > timeout[p][q] } ]
    /\ outbox' = outbox
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p][q] = last[p][q] + 1 |
                 q \in Proc]
    /\ clock' = [clock EXCEPT ![p] = ResetClock(p)]

Receive(p) ==
    /\ ~IsSend(p)
    /\ ~IsPredict(p)
    /\ \A m \in outbox[ q \in AllProcsExcept(p) ] :
          (m.type = "alive" /\ m.dst = p) => 
            /\ last' = [last EXCEPT ![p][m.src] = 0]
            /\ sus' = [sus EXCEPT ![p] = sus[p] \ {m.src}]
            /\ timeout' = [timeout EXCEPT ![p][m.src] = 
                             IF m.src \in sus[p] THEN timeout[p][m.src] + 1
                             ELSE timeout[p][m.src]]
    /\ UNCHANGED <<sus, outbox, clock>>
    /\ clock' = [clock EXCEPT ![p] = ResetClock(p)]

\* -----------------------------
\* Next-state relation for the whole system
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

\* -----------------------------
\* Specification
Spec == Init /\ [][Next]_<<sus, timeout, last, clock, outbox>>

\* -----------------------------
\* Type invariant (as required)
TypeOK ==
    /\ sus \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Message]

\* -----------------------------
\* The name of the invariant required by the .cfg
THEOREM SpecImpliesTypeOK == Spec => []TypeOK

====