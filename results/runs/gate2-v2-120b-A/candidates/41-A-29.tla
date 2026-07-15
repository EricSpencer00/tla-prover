---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval
    Messages       \* Set of possible alive messages, each simply a process id

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ProcList == Proc

LastHeardInit == [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
TimeOutInit  == [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
SuspectInit  == [p \in Proc |-> {}]
ClockInit    == [p \in Proc |-> 0]
OutboxInit   == [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    suspect,    \* [p \in Proc -> SUBSET Proc]
    timeout,    \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]
    lastHeard,  \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]
    clock,      \* [p \in Proc -> Nat]
    outbox      \* [p \in Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Type invariant (used also as the safety invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspect = SuspectInit
    /\ timeout = TimeOutInit
    /\ lastHeard = LastHeardInit
    /\ clock = ClockInit
    /\ outbox = OutboxInit
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {q : q \in Proc \ {p}}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ \A q \in Proc \ {p} :
          IF lastHeard[p][q] < timeout[p][q]
          THEN lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1]
          ELSE UNCHANGED lastHeard
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
          { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ \A q \in Proc \ {p} :
          IF lastHeard[p][q] < timeout[p][q]
          THEN lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1]
          ELSE UNCHANGED lastHeard
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ UNCHANGED clock
    /\ \A q \in Proc \ {p} :
         IF q \in outbox[q] \cup {p}  \* "alive" from q is present
         THEN /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q}]
              /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
              /\ timeout' = IF q \in suspect[p]
                             THEN [timeout EXCEPT ![p][q] = timeout[p][q] + 1]
                             ELSE UNCHANGED timeout
         ELSE UNCHANGED <<suspect, lastHeard, timeout>>
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ UNCHANGED <<clock>>

ClockReset(p) ==
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc \ {p} : clock[p] > timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

ProcStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ ClockReset(p)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc : ProcStep(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspect, timeout, lastHeard, clock, outbox>>

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
InitPred == Init          \* required name "Init"
TypeOKInv == TypeOK       \* required invariant name "TypeOK"

=============================================================================