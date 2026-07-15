---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Proc,        \* set of process identifiers
    d0,          \* default timeout interval (positive integer)
    SendPoint,   \* send interval (positive integer)
    PredictPoint,\* predict interval (positive integer)
    Messages     \* set of possible alive messages

(* ------------------------------------------------------------------- *)
(* State variables *)
VARIABLES
    suspicion,   \* [p \in Proc -> SUBSET Proc]  -- processes p suspects
    timeout,     \* [p \in Proc -> [q \in Proc -> Nat]] -- adaptive timeout per pair
    lastHeard,   \* [p \in Proc -> [q \in Proc -> Nat]] -- ticks since p last heard from q
    clock,       \* [p \in Proc -> Nat]          -- local clock per process
    outbox,      \* [p \in Proc -> SUBSET Messages] -- messages p wants to send this step
    inbox        \* [p \in Proc -> SUBSET Messages] -- messages received this step

(* ------------------------------------------------------------------- *)
(* Message definition *)
AliveMsg(p, q) == [type |-> "Alive", from |-> p, to |-> q]

(* ------------------------------------------------------------------- *)
(* Helper functions *)
ClockMultiple(p, k) == clock[p] % k = 0

AllProcs == Proc
Other(p) == Proc \ {p}

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]
    /\ inbox     = [p \in Proc |-> {}]

(* ------------------------------------------------------------------- *)
(* Actions *)

SendAlive(p) ==
    /\ ~ClockMultiple(p, PredictPoint)        \* not a predict step
    /\ ClockMultiple(p, SendPoint)            \* send step
    /\ outbox' = [outbox EXCEPT ![p] = {AliveMsg(p, q) : q \in Other(p)}]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ \A q \in Other(p):
          IF lastHeard[p][q] + 1 < timeout[p][q]
          THEN lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1]
          ELSE UNCHANGED lastHeard[p][q]
    /\ UNCHANGED <<suspicion, timeout, inbox>>

Predict(p) ==
    /\ ~ClockMultiple(p, SendPoint)           \* not a send step
    /\ ClockMultiple(p, PredictPoint)         \* predict step
    /\ \A q \in Other(p):
          IF lastHeard[p][q] > timeout[p][q]
          THEN suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup {q}]
          ELSE UNCHANGED suspicion[p]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ \A q \in Other(p):
          lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1]
    /\ UNCHANGED <<outbox, timeout, inbox>>

Receive(p) ==
    /\ \A q \in Other(p):
          IF \E m \in outbox[q] : /\ m.type = "Alive" /\ m.from = q /\ m.to = p
          THEN /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
               /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q}]
               /\ timeout'   = [timeout EXCEPT ![p][q] = timeout[p][q] + 1]
          ELSE UNCHANGED <<lastHeard[p], suspicion[p], timeout[p]>>
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ outbox'  = [outbox EXCEPT ![p] = {}]
    /\ inbox'   = [inbox EXCEPT ![p] = {}]
    /\ UNCHANGED <<suspicion, timeout, lastHeard>>

ResetClocks ==
    /\ \A p \in Proc :
          /\ clock[p] > SendPoint
          /\ clock[p] > PredictPoint
          /\ \A q \in Other(p) : clock[p] > timeout[p][q]
    /\ clock' = [p \in Proc |-> 0]
    /\ UNCHANGED <<suspicion, timeout, lastHeard, outbox, inbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ ResetClocks

(* ------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox, inbox>>

(* ------------------------------------------------------------------- *)
(* Safety invariant: TypeOK *)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]
    /\ inbox     \in [Proc -> SUBSET Messages]

=============================================================================