---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  CONSTANTS
--------------------------------------------------------------------*)
CONSTANTS
    Proc,          \* Set of processes
    d0,            \* Default timeout (positive integer)
    SendPoint,     \* Interval for sending alive messages (positive integer)
    PredictPoint,  \* Interval for making predictions (positive integer)
    Messages       \* Set of all possible messages

(*--------------------------------------------------------------------
  VARIABLES
--------------------------------------------------------------------*)
VARIABLES
    clock,         \* [p \in Proc |-> Nat]  local clocks
    suspicion,    \* [p \in Proc |-> SUBSET Proc]  suspicion sets
    timeout,      \* [p \in Proc |-> [q \in Proc |-> Nat]]  adaptive timeouts
    last,         \* [p \in Proc |-> [q \in Proc |-> Nat]]  last‑heard counters
    outbox,       \* [p \in Proc |-> SUBSET Messages]  messages to be sent
    chan          \* SUBSET Messages   channel of in‑flight messages

vars == <<clock, suspicion, timeout, last, outbox, chan>>

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
IsSendTick(p) == (clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0)
IsPredictTick(p) == (clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0)

AliveMsg(p, q) == [type |-> "Alive", from |-> p, to |-> q]

MaxTimeout(p) == 
    IF Proc = {} THEN 0
    ELSE Max({ timeout[p][q] : q \in Proc })

NextClock(p, c) ==
    LET maxT == Max({SendPoint, PredictPoint, MaxTimeout(p)})
    IN IF c > maxT THEN 0 ELSE c

IncLast(p, q) ==
    IF last[p][q] < timeout[p][q] THEN last[p][q] + 1 ELSE last[p][q]

(*--------------------------------------------------------------------
  Actions for a single process
--------------------------------------------------------------------*)
Send(p) ==
    /\ IsSendTick(p)
    /\ outbox' = [outbox EXCEPT ![p] = { AliveMsg(p, q) : q \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = NextClock(p, clock[p] + 1)]
    /\ suspicion' = suspicion
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p][q] = IncLast(p, q) 
                \* keep other entries unchanged
                \* (the EXCEPT clause only changes the specified entries)
                ]
    /\ UNCHANGED <<chan>>

Predict(p) ==
    /\ IsPredictTick(p)
    /\ let newSus == { q \in Proc \ {p} : last[p][q] > timeout[p][q] } IN
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
    /\ clock' = [clock EXCEPT ![p] = NextClock(p, clock[p] + 1)]
    /\ outbox' = outbox
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p][q] = IncLast(p, q) ]
    /\ UNCHANGED <<chan>>

Receive(p) ==
    /\ \lnot IsSendTick(p) /\ \lnot IsPredictTick(p)
    /\ let msgs == { m \in chan : m.to = p } IN
       \* Process each alive message addressed to p
       \* Compute updates for last, suspicion, timeout
       \* For each sender q, reset last[p][q] to 0 and remove q from suspicion.
       \* If q was already suspected, increase its timeout by 1.
       \* Remove processed messages from the channel.
       \* Other processes' state remains unchanged.
       \E q \in Proc :
          \* Determine whether a message from q is present
          ( ( \E m \in msgs : m.from = q ) =>
                /\ last' = [last EXCEPT ![p][q] = 0]
                /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q}]
                /\ timeout' = [timeout EXCEPT ![p][q] = 
                                IF q \in suspicion[p] THEN timeout[p][q] + 1
                                ELSE timeout[p][q]]
          )
    /\ clock' = [clock EXCEPT ![p] = NextClock(p, clock[p] + 1)]
    /\ outbox' = outbox
    /\ chan' = chan \ msgs

(*--------------------------------------------------------------------
  Global Next relation
--------------------------------------------------------------------*)
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ outbox = [p \in Proc |-> {}]
    /\ chan = {}

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ outbox \in [Proc -> SUBSET Messages]
    /\ chan \in SUBSET Messages

(*--------------------------------------------------------------------
  Example property (placeholder)
--------------------------------------------------------------------*)
Prop == TRUE

====