---- MODULE EPFailureDetector ----
(***************************************************************************)
(*  Eventually Perfect Failure Detector (Chandra & Toueg, 1996).           *)
(*  Each process periodically sends alive messages and periodically      *)
(*  updates its suspicion set based on adaptive timeout intervals.         *)
(*  The send and predict operations are separated by distinct clock       *)
(*  ticks (SendPoint and PredictPoint), so they never coincide.           *)
(*  Correct processes are eventually no longer suspected.                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint > 0 /\ PredictPoint > 0 /\ SendPoint # PredictPoint

\* Timeout intervals are bounded by d0 + 1 so the state space stays finite.
\* The adaptive timeout increases by at most 1 per prediction cycle.
\* The maximum timeout is d0 + 1, which is the eventual perfect bound.
\* The send and predict intervals are chosen so that SendPoint and
\* PredictPoint are not multiples of each other, guaranteeing that
\* send and predict ticks never coincide.
\* The message set is a finite set of tuples (src, dst, kind).
\* For simplicity, we model only alive messages; the message type is
\* encoded as a string "alive".
\* The outgoing message set is per-process; the controller module
\* (not shown) would deliver these messages to the recipients.
\* The local clock is per-process and bounded by the maximum of
\* SendPoint, PredictPoint, and d0 + 1.
\* The last-heard counter is the number of ticks since the last alive
\* message was received from a given process.
\* The timeout interval is the current threshold for suspecting a
\* process; it grows adaptively when a suspected process sends a message.
\* The suspicion set is the set of processes currently believed crashed.
\* The type invariant bounds all state components.
\* The specification is the nondeterministic interleaving of the three
\* per-process actions: SendAlive, Predict, and Receive.
\* The model is finite and checkable with TLC.

VARIABLES suspicion, timeout, lastHeard, clock, outMsg

vars == << suspicion, timeout, lastHeard, clock, outMsg >>

\* A process's local clock ticks from 0 up to the maximum of the
\* send interval, predict interval, and the maximum timeout.
MaxClock == SendPoint + PredictPoint + (d0 + 1)

Init == /\ suspicion = [p \in Proc |-> {}]
        /\ timeout   = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
        /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
        /\ clock     = [p \in Proc |-> 0]
        /\ outMsg    = [p \in Proc |-> {}]

\* SendAlive: at a multiple of SendPoint (but not PredictPoint),
\* the process broadcasts alive messages to all other processes.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outMsg' = [outMsg EXCEPT ![p] = Messages]
    /\ \E q \in Proc \ {p} :
          /\ lastHeard[p][q] < timeout[p][q]
          /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
    /\ UNCHANGED << suspicion, timeout, clock >>

\* Predict: at a multiple of PredictPoint (but not SendPoint),
\* the process updates its suspicion set based on the timeout intervals.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = {q \in Proc \ {p} :
                                            lastHeard[p][q] >= timeout[p][q]}]
    /\ \E q \in Proc \ {p} :
          /\ lastHeard[p][q] < timeout[p][q]
          /\ lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1]
    /\ UNCHANGED << timeout, outMsg, clock >>

\* Receive: at all other clock values, the process receives any
\* alive messages it has in its outgoing set.  For each such message,
\* the corresponding last-heard counter is reset to 0, the sender is
\* removed from the suspicion set, and if the sender was suspected,
\* its timeout interval is increased by 1 (adaptive timeout).
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E m \in outMsg[p] :
          /\ m[1] \in Proc \ {p}
          /\ lastHeard' = [lastHeard EXCEPT ![p][m[1]] = 0]
          /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {m[1]}]
          /\ timeout'   = [timeout   EXCEPT ![p][m[1]] = Min(timeout[p][m[1]] + 1, d0 + 1)]
    /\ outMsg' = [outMsg EXCEPT ![p] = outMsg[p] \ {m}]
    /\ UNCHANGED clock

\* Tick: advance the local clock, wrapping around at MaxClock.
Tick(p) ==
    /\ clock[p] < MaxClock
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED << suspicion, timeout, lastHeard, outMsg >>

Next == \E p \in Proc :
            SendAlive(p) \/ Predict(p) \/ Receive(p) \/ Tick(p)

Spec == Init /\ [][Next]_vars

\* Type invariant: all state components are finite and well-typed.
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> 0 .. d0 + 1]]
    /\ lastHeard \in [Proc -> [Proc -> 0 .. d0 + 1]]
    /\ clock     \in [Proc -> 0 .. MaxClock]
    /\ outMsg    \in [Proc -> SUBSET Messages]
====