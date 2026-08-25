---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Proc,               \* The set of processes
    d0,                 \* Default timeout value (Nat)
    SendPoint,          \* Positive send interval (Nat)
    PredictPoint,       \* Positive predict interval (Nat)
    Messages            \* The set of possible messages

VARIABLES 
    clock,      \* [Proc -> Nat]  local clocks
    suspect,    \* [Proc -> SUBSET Proc]  suspicion sets
    timeout,    \* [Proc -> [Proc -> Nat]]  adaptive timeouts
    last,       \* [Proc -> [Proc -> Nat]]  counters since last heard
    out,        \* [Proc -> SUBSET Messages]  outgoing messages of each process
    chan        \* SUBSET Messages  the communication channel (handled externally)

\*=====================================================================
\* Helper definitions
\*---------------------------------------------------------------------
\* The maximum relevant threshold for a process p: the larger of the
\* send interval, predict interval, and all current timeout values.
\*---------------------------------------------------------------------
MaxThresh(p) == 
    Max( {SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc \ {p} } )

\* Clock update with wrap‑around when exceeding MaxThresh(p)
\*---------------------------------------------------------------------
NextClock(p, c) == 
    LET n == c + 1 IN
    IF n > MaxThresh(p) THEN 0 ELSE n

\* A concrete representation of an "alive" message
\*---------------------------------------------------------------------
AliveMsg(p,q) == [sender |-> p, receiver |-> q, mtype |-> "alive"]

\*=====================================================================
\* Initialization
\*---------------------------------------------------------------------
Init == 
    /\ clock   = [p \in Proc |-> 0]
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ out     = [p \in Proc |-> {}]
    /\ chan    = {}

\*=====================================================================
\* Type invariant
\*---------------------------------------------------------------------
TypeOK == 
    /\ clock   \in [Proc -> Nat]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last    \in [Proc -> [Proc -> Nat]]
    /\ out     \in [Proc -> SUBSET Messages]
    /\ chan    \in SUBSET Messages
    /\ \A p \in Proc : suspect[p] \subseteq Proc \ {p}
    /\ \A p,q \in Proc : timeout[p][q] >= 0

\*=====================================================================
\* Process actions
\*---------------------------------------------------------------------

\* Send alive messages (clock at a multiple of SendPoint, not PredictPoint)
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = { AliveMsg(p,q) : q \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = NextClock(p, clock[p])]
    /\ UNCHANGED <<suspect, timeout, last, chan>>

\* Predict crashes (clock at a multiple of PredictPoint, not SendPoint)
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup 
                    { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = NextClock(p, clock[p])]
    /\ UNCHANGED <<out, timeout, last, chan>>

\* Receive incoming alive messages (any other clock value)
Receive(p) ==
    /\ ~(
          (clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0) \/
          (clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
       )
    /\ 
       \E q \in Proc \ {p} :
           (* there is an alive message from q to p in the channel *)
           AliveMsg(q,p) \in chan
           /\ 
              \* Update state after receiving that message
              LET newLast == [last EXCEPT ![p][q] = 0]               IN
              LET newSuspect == [suspect EXCEPT ![p] = suspect[p] \ {q}] IN
              LET newTimeout == 
                 [timeout EXCEPT ![p][q] = 
                     IF q \in suspect[p] THEN timeout[p][q] + 1 
                     ELSE timeout[p][q]]                         IN
              /\ last'    = newLast
              /\ suspect' = newSuspect
              /\ timeout' = newTimeout
              /\ chan'    = chan \ {AliveMsg(q,p)}
              /\ clock'   = [clock EXCEPT ![p] = NextClock(p, clock[p])]
              /\ out'     = out
    \/  (* no alive message addressed to p *)
        /\ \A m \in chan : m.receiver # p \/ m.mtype # "alive"
        /\ UNCHANGED <<clock, suspect, timeout, last, out, chan>>

\* Choose one process to act
ProcAction == 
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

\*=====================================================================
\* Next-state relation
\*---------------------------------------------------------------------
Next == ProcAction

\*=====================================================================
\* Specification
\*---------------------------------------------------------------------
Spec == Init /\ [][Next]_<<clock, suspect, timeout, last, out, chan>>

\*=====================================================================
\* Invariants and properties
\*---------------------------------------------------------------------
INVARIANTS TypeOK

\* No additional properties are required for this model
\*=====================================================================
====