---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,        \* the set of processes
  d0,          \* default initial timeout interval
  SendPoint,   \* clock value that triggers sending alive messages
  PredictPoint, \* clock value that triggers making crash predictions
  Messages     \* the set of possible alive-message destinations

\* Each process maintains a suspicion set, a per-process timeout interval,
\* a per-process last-heard counter, a local clock, and pending outgoing messages.
VARIABLES
  suspect,   \* suspect[p]: processes p currently suspects to have crashed
  timeout,   \* timeout[p]: timeout interval p uses for each other process
  lastHeard, \* lastHeard[p]: [Proc -> Nat] ticks since p last heard from each process
  clock,     \* clock[p]: p's local clock value
  outgoing   \* outgoing[p]: messages p intends to send this transition

vars == << suspect, timeout, lastHeard, clock, outgoing >>

MaxClock == 2
MaxTimeout == 1

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

\* Send alive messages on the send schedule; only fires when the clock is not
\* also on the predict schedule, so the two actions never coincide.
SendAlive(p) ==
  /\ clock[p] = SendPoint
  /\ SendPoint # PredictPoint
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m # p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q]
                      THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED << suspect, timeout >>

\* Make crash predictions on the separate prediction schedule.
Predict(p) ==
  /\ clock[p] = PredictPoint
  /\ SendPoint # PredictPoint
  /\ suspect' = [suspect EXCEPT ![p] = 
        {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q]
                      THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED << timeout, outgoing >>

\* Receive any arriving alive messages; a message from a suspected process
\* both clears the suspicion and expands that process's timeout.
Receive(p, m) ==
  /\ m \in outgoing[p]
  /\ outgoing' = [outgoing EXCEPT ![p] = outgoing[p] \ {m}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [lastHeard[p] EXCEPT ![m] = 0]]
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m}]
  /\ timeout' = [timeout EXCEPT ![p] = [timeout[p] EXCEPT ![m] = 
        @ + (IF m \in suspect[p] THEN 1 ELSE 0)]]
  /\ UNCHANGED << clock >>

\* Clock values wrap within a bounded window to keep the model finite.
Tick(p) ==
  /\ clock[p] >= MaxClock
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED << suspect, timeout, lastHeard, outgoing >>

Next ==
  \E p \in Proc :
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Tick(p)
    \/ \E m \in Messages : Receive(p, m)

\* Type-checking sanity: last-heard counters and timeouts are integers, and
\* the other fields stay within their modeled shapes.
TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> 0..MaxTimeout]]
  /\ timeout \in [Proc -> [Proc -> 0..MaxTimeout]]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ outgoing \in [Proc -> SUBSET Messages]
  /\ clock \in [Proc -> 0..MaxClock]

Spec == Init /\ [][Next]_vars

====