---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants (to be bound in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer, not a multiple of PredictPoint)
    PredictPoint,  \* Predict interval (positive integer, not a multiple of SendPoint)
    Messages       \* Set of possible messages (will be defined below)

(*--------------------------------------------------------------------
  Message type
--------------------------------------------------------------------*)
Message == [from : Proc, to : Proc, type : {"Alive"}]

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]   -- processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] -- adaptive timeout per peer
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] -- ticks since last alive from q
    clock,       \* [p \in Proc |-> Nat]           -- local logical clock
    outbox,      \* [p \in Proc |-> SUBSET Message] -- messages p will send this step
    channel      \* SUBSET Message                -- global unordered message channel

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Self := [p \in Proc |-> p]  \* identity map, convenient for type checking

Neighbors(p) == Proc \ {p}

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]
    /\ channel   = {}

(*--------------------------------------------------------------------
  SendAlive action (executes when clock mod SendPoint == 0 and not predict)
--------------------------------------------------------------------*)
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { [from |-> p, to |-> q, type |-> "Alive"] :
                                          q \in Neighbors(p) }]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ \A q \in Neighbors(p) :
          IF lastHeard[p][q] < timeout[p][q]
          THEN lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1]
          ELSE UNCHANGED lastHeard
    /\ UNCHANGED <<suspicion, timeout, channel>>

(*--------------------------------------------------------------------
  Predict action (executes when clock mod PredictPoint == 0 and not send)
--------------------------------------------------------------------*)
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT
          ![p] = { q \in Neighbors(p) :
                     lastHeard[p][q] >= timeout[p][q] } \cup suspicion[p]]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ \A q \in Neighbors(p) :
          lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1]
    /\ UNCHANGED <<timeout, outbox, channel>>

(*--------------------------------------------------------------------
  Receive action (executes at all other clock values)
--------------------------------------------------------------------*)
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ LET incoming == { m \in channel :
                           /\ m.type = "Alive"
                           /\ m.to   = p }
       IN
       /\ IF incoming = {} THEN UNCHANGED <<suspicion, timeout, lastHeard>>
          ELSE
            /\ suspicion' = [suspicion EXCEPT
                  ![p] = suspicion[p] \ { m.from : m \in incoming }]
            /\ timeout' = [timeout EXCEPT
                  ![p][m.from] = IF m.from \in suspicion[p] THEN @ + 1 ELSE @
                                   \* adaptive increase when a suspected process sends
                                   \* (if not suspected, timeout unchanged)
                  | m \in incoming]
            /\ lastHeard' = [lastHeard EXCEPT
                  ![p][m.from] = 0
                  | m \in incoming]
       /\ channel' = channel \ incoming
       /\ clock' = [clock EXCEPT ![p] = @ + 1]
       /\ UNCHANGED outbox

(*--------------------------------------------------------------------
  Clock wrap-around (reset) to keep the clock domain finite
--------------------------------------------------------------------*)
WrapClock(p) ==
    /\ clock[p] > Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspicion, timeout, lastHeard, outbox, channel>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : WrapClock(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox, channel>>

(*--------------------------------------------------------------------
  Type invariant (the only invariant required by the .cfg)
--------------------------------------------------------------------*)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]
    /\ channel   \in SUBSET Message

====