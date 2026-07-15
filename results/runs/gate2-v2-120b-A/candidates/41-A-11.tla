---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS
    Proc,            \* Set of process identifiers
    d0,              \* Default timeout interval (positive integer)
    SendPoint,       \* Send interval (positive integer)
    PredictPoint,    \* Predict interval (positive integer)
    Messages         \* Set of possible messages (including alive messages)

(*-----------------------------------------------------------------
  Derived definitions
-----------------------------------------------------------------*)
Other(p) == Proc \ {p}

(*-----------------------------------------------------------------
  Message definition
-----------------------------------------------------------------*)
Message == [type : {"alive"},
            from : Proc,
            to   : Proc]

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]   -- set of processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc -> Nat]]  -- timeout interval per pair
    lastSeen,    \* [p \in Proc |-> [q \in Proc -> Nat]]  -- ticks since last alive from q
    clock,       \* [p \in Proc -> Nat]  -- local clock per process
    outbox       \* [p \in Proc -> SUBSET Message]  -- messages p wants to send

(*-----------------------------------------------------------------
  Type invariant (also required as TypeOK)
-----------------------------------------------------------------*)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastSeen  \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]
    /\ \A p \in Proc:
          /\ suspicion[p] \subseteq Proc
          /\ timeout[p][p] = 0               \* trivial entry for self
          /\ \A q \in Other(p): timeout[p][q] >= 0
          /\ \A q \in Proc: lastSeen[p][q] >= 0
          /\ \A m \in outbox[p]:
                /\ m.type = "alive"
                /\ m.from = p
                /\ m.to   \in Other(p)

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastSeen  = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Helper to create alive messages addressed to all other processes
-----------------------------------------------------------------*)
AliveMsgs(p) == { [type |-> "alive", from |-> p, to |-> q] : q \in Other(p) }

(*-----------------------------------------------------------------
  SendAlive action for a single process p
-----------------------------------------------------------------*)
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = AliveMsgs(p)]
    /\ \A q \in Other(p):
          IF q \in suspicion[p]
             THEN lastSeen'[p][q] = lastSeen[p][q] + 1
             ELSE lastSeen'[p][q] = lastSeen[p][q] + 1
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<suspicion, timeout>>

(*-----------------------------------------------------------------
  Predict action for a single process p
-----------------------------------------------------------------*)
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = { q \in Other(p) :
                                          lastSeen[p][q] >= timeout[p][q] }]
    /\ \A q \in Other(p):
          lastSeen'[p][q] = lastSeen[p][q] + 1
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<outbox, timeout>>

(*-----------------------------------------------------------------
  Receive action for a single process p
-----------------------------------------------------------------*)
Receive(p) ==
    /\ ~ (clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~ (clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ \A m \in outbox[p]:
          /\ m.type = "alive"
          /\ m.from \in Other(p) /\ m.to = p
    /\ \A q \in Other(p):
          IF q \in { m.from : m \in outbox[q] }   \* there is an alive from q to p
             THEN /\ lastSeen'[p][q] = 0
                  /\ suspicion'[p] = suspicion[p] \ { q }
                  /\ IF q \in suspicion[p]
                        THEN timeout'[p][q] = timeout[p][q] + 1
                        ELSE timeout'[p][q] = timeout[p][q]
             ELSE /\ lastSeen'[p][q] = lastSeen[p][q] + 1
                  /\ UNCHANGED <<suspicion, timeout>>
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > Max(SendPoint, PredictPoint,
                                          Max({ timeout[p][r] : r \in Other(p)}))
                              THEN 0
                              ELSE clock[p] + 1]
    /\ UNCHANGED <<suspicion, timeout>>

(*-----------------------------------------------------------------
  Next-state relation: choose a process and apply exactly one of its actions
-----------------------------------------------------------------*)
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<suspicion, timeout, lastSeen, clock, outbox>>

(*-----------------------------------------------------------------
  Safety invariant (already defined as TypeOK)
-----------------------------------------------------------------*)
SafetyInv == TypeOK

=============================================================================