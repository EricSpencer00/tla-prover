---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of possible messages (must include alive messages)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Message == [type : {"alive"}, src : Proc, dst : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc] : processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] : timeout interval p uses for q
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] : ticks since p last heard from q
    clock,       \* [p \in Proc |-> Nat] : local clock of each process
    outbox       \* [p \in Proc |-> SUBSET Message] : messages p will send this step

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllProcsExcept(p) == Proc \ {p}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { [type |-> "alive", src |-> p, dst |-> q] : q \in AllProcsExcept(p) }]
    /\ clock'   = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = IF q \in AllProcsExcept(p) THEN @ + 1 ELSE @
                                          FOR q \in AllProcsExcept(p)]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup
                     { q \in AllProcsExcept(p) :
                         lastHeard[p][q] > timeout[p][q] }]
    /\ clock'   = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1
                                          FOR q \in AllProcsExcept(p)]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ \A q \in AllProcsExcept(p) :
          \A m \in outbox[q] :
              (m.type = "alive" /\ m.dst = p) =>
                 /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
                 /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q}]
                 /\ timeout'   = [timeout EXCEPT ![p][q] = IF q \in suspicion[p] THEN @ + 1 ELSE @]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ UNCHANGED <<suspicion, timeout, lastHeard>>

ResetClocks ==
    /\ \A p \in Proc :
          clock[p] > SendPoint /\ clock[p] > PredictPoint /\
          \A q \in AllProcsExcept(p) : clock[p] > timeout[p][q]
    /\ clock' = [p \in Proc |-> 0]
    /\ UNCHANGED <<suspicion, timeout, lastHeard, outbox>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ ResetClocks

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox>>

\* ----------------------------------------------------------------------
\* Type invariant (required by the .cfg)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Theorem (optional, not required by the .cfg but useful)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====