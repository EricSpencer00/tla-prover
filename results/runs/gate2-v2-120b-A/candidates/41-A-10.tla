---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,           \* Set of process identifiers
    d0,             \* Default timeout interval (positive integer)
    SendPoint,      \* Periodic send interval (positive integer)
    PredictPoint,   \* Periodic predict interval (positive integer)
    Messages        \* Set of message identifiers (e.g., {"alive"})

\* ----------------------------------------------------------------------
\* Types for clarity
\* ----------------------------------------------------------------------
Msg == [src : Proc, dst : Proc, typ : Messages]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    clock,          \* [p \in Proc -> Nat]   local clock of each process
    susp,           \* [p \in Proc -> SUBSET Proc]   suspicion set of each process
    timeout,        \* [p \in Proc -> [q \in Proc -> Nat]]   timeout interval per peer
    lastHeard,      \* [p \in Proc -> [q \in Proc -> Nat]]   ticks since last alive from q
    outbox,         \* [p \in Proc -> SUBSET Msg]   messages a process will send this step
    inbox           \* [p \in Proc -> SUBSET Msg]   messages a process receives this step

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ susp  = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ outbox = [p \in Proc |-> {}]
    /\ inbox  = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllPeers(p) == { q \in Proc : q # p }

\* Send alive messages to every other process
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0          \* send and predict never coincide
    /\ outbox' = [outbox EXCEPT ![p] = { [src |-> p, dst |-> q, typ |-> "alive"]
                                           : q \in AllPeers(p) } ]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = 
                         [q \in Proc |-> 
                            IF timeout[p][q] > lastHeard[p][q] 
                               THEN lastHeard[p][q] + 1 
                               ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<susp, timeout, inbox>>

\* Predict: suspect any process whose silence exceeds its timeout
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ susp' = [susp EXCEPT ![p] = 
                    { q \in AllPeers(p) : lastHeard[p][q] > timeout[p][q] } \cup
                    susp[p]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = 
                         [q \in Proc |-> lastHeard[p][q] + 1]]
    /\ UNCHANGED <<outbox, timeout, inbox>>

\* Receive: process all messages currently in its inbox
Receive(p) ==
    /\ outbox[p] = {}          \* no send or predict this step
    /\ clock'[p] = 
          IF clock[p] >= Max({SendPoint, PredictPoint} \cup 
                             { timeout[p][q] : q \in AllPeers(p) })
          THEN 0
          ELSE clock[p] + 1
    /\ LET msgs == inbox[p] IN
       /\ susp' = [susp EXCEPT ![p] = 
                    { q \in susp[p] :
                        ~(\E m \in msgs : m.src = q /\ m.typ = "alive") }]
       /\ timeout' = [timeout EXCEPT 
                        ![p] = 
                          [q \in Proc |-> 
                            IF (\E m \in msgs : m.src = q /\ m.typ = "alive") 
                               /\ q \in susp[p]
                            THEN timeout[p][q] + 1
                            ELSE timeout[p][q]]]
       /\ lastHeard' = [lastHeard EXCEPT 
                         ![p] = 
                           [q \in Proc |-> 
                               IF (\E m \in msgs : m.src = q /\ m.typ = "alive")
                               THEN 0
                               ELSE lastHeard[p][q] + 1]]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ inbox'  = [inbox EXCEPT ![p] = {}]
    /\ UNCHANGED <<susp, timeout, lastHeard>>

\* ----------------------------------------------------------------------
\* Process step (nondeterministic choice of which processes act)
\* ----------------------------------------------------------------------
ProcessStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)

Next ==
    /\ \E p \in Proc : ProcessStep(p)
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<clock, susp, timeout, lastHeard, outbox, inbox>>

\* ----------------------------------------------------------------------
\* Type invariant (as required)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ susp  \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ outbox \in [Proc -> SUBSET Msg]
    /\ inbox \in [Proc -> SUBSET Msg]
    /\ \A p \in Proc : outbox[p] \subseteq { [src |-> p, dst |-> q, typ |-> "alive"] : q \in AllPeers(p) }
    /\ \A p \in Proc : inbox[p] \subseteq { [src |-> q, dst |-> p, typ |-> "alive"] : q \in AllPeers(p) }

\* ----------------------------------------------------------------------
\* Theorem (optional, not required by the cfg but kept for completeness)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====