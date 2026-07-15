---- MODULE EPFailureDetector ----
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------
  Constants (must be supplied in the .cfg)
--------------------------------------------------------------------*)
CONSTANTS 
    Proc,            \* Set of processes
    d0,              \* Default timeout interval (positive integer)
    SendPoint,       \* Send interval (positive integer)
    PredictPoint,    \* Predict interval (positive integer)
    Messages         \* Set of possible messages (including alive msgs)

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
ProcSet == Proc

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Message == [from : Proc, to : Proc, type : {"alive"}]

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES 
    suspicion,   \* [p \in Proc |-> SUBSET Proc] : processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc -> Nat]] : timeout intervals
    lastHeard,   \* [p \in Proc |-> [q \in Proc -> Nat]] : ticks since last alive from q
    clock,       \* [p \in Proc -> Nat] : local clock of each process
    outbox       \* [p \in Proc -> SUBSET Message] : messages p will send this step

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
AliveMsg(p, q) == [from |-> p, to |-> q, type |-> "alive"]

AllOther(p) == Proc \ {p}

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Send-alive action (when clock is a multiple of SendPoint but not PredictPoint)
--------------------------------------------------------------------*)
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = 
          { AliveMsg(p, q) : q \in AllOther(p) }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT 
          ![p][q] = IF q \in AllOther(p) THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] 
          \* we increment all counters; timeout logic is handled in Predict
          ]
    /\ UNCHANGED <<suspicion, timeout>>

(*--------------------------------------------------------------------
  Predict action (when clock is a multiple of PredictPoint but not SendPoint)
--------------------------------------------------------------------*)
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ \A q \in AllOther(p): 
          (lastHeard[p][q] > timeout[p][q]) => q \in suspicion[p]
    /\ suspicion' = [suspicion EXCEPT ![p] = 
          { q \in suspicion[p] : lastHeard[p][q] <= timeout[p][q] } 
          \cup { q \in AllOther(p) : lastHeard[p][q] > timeout[p][q] }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT 
          ![p][q] = IF q \in AllOther(p) THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
    /\ UNCHANGED <<timeout, outbox>>

(*--------------------------------------------------------------------
  Receive action (any other clock value)
--------------------------------------------------------------------*)
Receive(p) ==
    /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ \A m \in outbox[p] :
          /\ m.type = "alive"
          /\ m.to \in Proc
          /\ m.from \in Proc
    /\ \E recv \subseteq outbox[p] :
          /\ \A m \in recv : m.type = "alive"
          /\ \A q \in AllOther(p) :
                IF q \in { m.from : m \in recv } 
                THEN /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
                     /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q}]
                     /\ timeout' = 
                         IF q \in suspicion[p] 
                         THEN [timeout EXCEPT ![p][q] = timeout[p][q] + 1]
                         ELSE timeout
                ELSE /\ lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1]
                     /\ UNCHANGED <<suspicion, timeout>>
          /\ outbox' = [outbox EXCEPT ![p] = {}]
          /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]

(*--------------------------------------------------------------------
  Clock wrap‑around (reset to 0 when exceeding all relevant thresholds)
--------------------------------------------------------------------*)
ClockReset(p) ==
    /\ \E t \in Nat :
          t > SendPoint /\ t > PredictPoint /\
          \A q \in AllOther(p) : t > timeout[p][q]
    /\ clock[p] > SendPoint /\ clock[p] > PredictPoint /\
       \A q \in AllOther(p) : clock[p] > timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspicion, timeout, lastHeard, outbox>>

(*--------------------------------------------------------------------
  Per‑process step (one of the three actions or a clock reset)
--------------------------------------------------------------------*)
ProcStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ ClockReset(p)

(*--------------------------------------------------------------------
  Global next-state relation
--------------------------------------------------------------------*)
Next ==
    \E p \in Proc : ProcStep(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type invariant required by the .cfg file
--------------------------------------------------------------------*)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]

(*--------------------------------------------------------------------
  The identifier required by the .cfg file
--------------------------------------------------------------------*)
INVARIANTS == TypeOK

====