---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES suspicion, timeout, last, clock, outbox

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
SendTimes == { n * SendPoint : n \in Nat }
PredictTimes == { n * PredictPoint : n \in Nat }

MaxTimeout(p) == 
  LET T == { timeout[p][q] : q \in Proc \ {p} } 
  IN IF T = {} THEN 0 ELSE Max(T)

NewClock(p) == 
  LET M == Max({SendPoint, PredictPoint, MaxTimeout(p)}) 
  IN IF clock[p] + 1 > M THEN 0 ELSE clock[p] + 1

AliveMessage(p, q) == [src |-> p, dst |-> q, type |-> "alive"]

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
/\ suspicion = [p \in Proc |-> {}]
/\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
/\ last      = [p \in Proc |-> [q \in Proc |-> 0]]
/\ clock     = [p \in Proc |-> 0]
/\ outbox    = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
SendAlive(p) ==
/\ clock[p] \in SendTimes
/\ clock[p] \notin PredictTimes
/\ outbox' = [outbox EXCEPT ![p] = { AliveMessage(p, q) : q \in Proc \ {p} }]
/\ suspicion' = suspicion
/\ timeout'   = timeout
/\ last' = [last EXCEPT ![p][q] = 
               IF last[p][q] < timeout[p][q] THEN last[p][q] + 1 ELSE last[p][q] 
               \* for all q \in Proc
           ]
/\ clock' = [clock EXCEPT ![p] = NewClock(p)]
/\ UNCHANGED << suspicion, timeout, last, clock, outbox >> \* other processes unchanged

Predict(p) ==
/\ clock[p] \in PredictTimes
/\ clock[p] \notin SendTimes
/\ newSuspects == { q \in Proc \ {p} : last[p][q] > timeout[p][q] }
/\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSuspects]
/\ timeout'   = timeout
/\ last' = [last EXCEPT ![p][q] = 
               IF last[p][q] < timeout[p][q] THEN last[p][q] + 1 ELSE last[p][q] 
           ]
/\ outbox' = outbox
/\ clock' = [clock EXCEPT ![p] = NewClock(p)]
/\ UNCHANGED << suspicion, timeout, last, outbox, clock >> \* other processes unchanged

Receive(p) ==
/\ clock[p] \notin SendTimes
/\ clock[p] \notin PredictTimes
/\ \* nondeterministically choose the set of processes from which p receives an alive message
   \E rec \in SUBSET (Proc \ {p}) :
     /\ (* update suspicion: remove those from which a message is received *)
        suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ rec]
     /\ (* reset last‑heard counters for senders, increment others if not timed out *)
        last' = [last EXCEPT 
                  ![p][q] = 
                    IF q \in rec THEN 0
                    ELSE IF last[p][q] < timeout[p][q] THEN last[p][q] + 1
                    ELSE last[p][q] ]
     /\ (* adaptive timeout increase for correctly suspected processes that sent a message *)
        timeout' = [timeout EXCEPT 
                     ![p][q] = 
                       IF q \in rec /\ q \in suspicion[p] THEN timeout[p][q] + 1
                       ELSE timeout[p][q] ]
     /\ outbox' = outbox
     /\ clock' = [clock EXCEPT ![p] = NewClock(p)]
     /\ UNCHANGED << suspicion, timeout, last, outbox, clock >> \* other processes unchanged

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<suspicion, timeout, last, clock, outbox>>

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeOK ==
/\ suspicion \in [Proc -> SUBSET Proc]
/\ timeout   \in [Proc -> [Proc -> Nat]]
/\ last      \in [Proc -> [Proc -> Nat]]
/\ clock     \in [Proc -> Nat]
/\ outbox    \in [Proc -> SUBSET Messages]

(*--------------------------------------------------------------------
  Required identifiers for the .cfg file
--------------------------------------------------------------------*)
INIT == Init
NEXT == Next
INVARIANTS == TypeOK
SPECIFICATION == Spec
PROPERTIES == TRUE

====