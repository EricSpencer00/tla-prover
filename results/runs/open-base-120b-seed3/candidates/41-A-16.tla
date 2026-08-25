---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (to be supplied by the configuration)
--------------------------------------------------------------------*)
CONSTANTS
    Proc,        \* Set of process identifiers
    d0,          \* Default timeout interval (positive integer)
    SendPoint,   \* Send interval (positive integer)
    PredictPoint,\* Predict interval (positive integer)
    Messages     \* Set of all possible messages

(*--------------------------------------------------------------------
  Message type (alive messages)
--------------------------------------------------------------------*)
Message == [type : {"Alive"}, src : Proc, dst : Proc]

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]  -- suspected processes of p
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- timeout intervals
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive from q
    clock,       \* [p \in Proc |-> Nat]                -- local clock of p
    outgoing     \* [p \in Proc |-> SUBSET Messages]    -- messages p wants to send

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
IsMultiple(x, n) == \E k \in Nat : x = k * n

IncCounters(p, incSet) ==
    [lastHeard EXCEPT ![p][q] = IF q \in incSet THEN @ + 1 ELSE @]

IncAllCounters(p) == IncCounters(p, Proc)

ResetCounter(p, q) ==
    [lastHeard EXCEPT ![p][q] = 0]

AddSuspects(p, new) ==
    [suspicion EXCEPT ![p] = @ \cup new]

RemoveSuspects(p, rem) ==
    [suspicion EXCEPT ![p] = @ \setminus rem]

IncTimeout(p, q) ==
    [timeout EXCEPT ![p][q] = @ + 1]

SetOutgoingAlive(p) ==
    [outgoing EXCEPT ![p] = { m \in Messages :
                                 /\ m.type = "Alive"
                                 /\ m.src = p
                                 /\ m.dst \in Proc \ {p} }]

AdvanceClock(p) ==
    [clock EXCEPT ![p] = @ + 1]

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outgoing  = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Process actions
--------------------------------------------------------------------*)
SendAlive(p) ==
    /\ IsMultiple(clock[p], SendPoint)
    /\ ~IsMultiple(clock[p], PredictPoint)
    /\ outgoing' = SetOutgoingAlive(p)
    /\ clock'    = AdvanceClock(p)
    /\ lastHeard' = IncCounters(p, Proc \ suspicion[p])
    /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
    /\ IsMultiple(clock[p], PredictPoint)
    /\ ~IsMultiple(clock[p], SendPoint)
    /\ let newSuspects == { q \in Proc : lastHeard[p][q] > timeout[p][q] } in
       suspicion' = AddSuspects(p, newSuspects)
    /\ clock'    = AdvanceClock(p)
    /\ lastHeard' = IncAllCounters(p)
    /\ UNCHANGED << timeout, outgoing >>

Receive(p) ==
    /\ ~IsMultiple(clock[p], SendPoint)
    /\ ~IsMultiple(clock[p], PredictPoint)
    /\ \E R \in SUBSET Proc :
          /\ (* R is the set of processes from which p receives an alive message *)
             \A q \in R : q # p
          /\ (* Update counters for received messages *)
             suspicion' = RemoveSuspects(p, R)
          /\ lastHeard' = [lastHeard EXCEPT
                              ![p][q] = IF q \in R THEN 0 ELSE @ + 1
                          ]
          /\ timeout' = [timeout EXCEPT
                           ![p][q] = IF q \in (suspicion[p] \cap R) THEN @ + 1 ELSE @
                       ]
          /\ clock' = AdvanceClock(p)
          /\ UNCHANGED outgoing
    /\ UNCHANGED << >>  \* (no other variables)

(*--------------------------------------------------------------------
  Next-state relation (interleaving of process actions)
--------------------------------------------------------------------*)
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outgoing  \in [Proc -> SUBSET Messages]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outgoing>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
THEOREM TypeInvariant == Spec => []TypeOK

=============================================================================