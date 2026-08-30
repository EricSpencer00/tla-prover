---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* A "process" is both a sender and a receiver in this failure detector
\* model: it periodically sends alive messages, announces no news, and
\* separately predicts based on what it has (not) heard from others.
\* These two actions are deliberately timed to never fire at once.
\* LastHeard[p] is a per-sender counter of ticks; it is what drives
\* every suspicion decision -- an absolute wall-clock is *not* modeled.
\* AdaptiveTimeOuts records the timeout each receiver is running for a
\* given sender's messages, which the spec bumps whenever a suspected
\* sender actually reaches it -- that bump is the *self-correcting* step.

VARIABLES Suspicion, AdaptiveTimeOuts, LastHeard, Clock, Outbox

vars == <<Suspicion, AdaptiveTimeOuts, LastHeard, Clock, Outbox>>

Zero == [p \in Proc |-> 0]

TypeOK ==
    /\ LastHeard \in [Proc -> Nat]
    /\ AdaptiveTimeOuts \in [Proc -> Nat]
    /\ Suspicion \in [Proc -> SUBSET Proc]
    /\ Clock \in [Proc -> Nat]
    /\ Outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ Suspicion = [p \in Proc |-> {}]
    /\ AdaptiveTimeOuts = [p \in Proc |-> d0]
    /\ LastHeard = [p \in Proc |-> Zero]
    /\ Clock = [p \in Proc |-> 0]
    /\ Outbox = [p \in Proc |-> {}]

Bump(t) == IF t < SendPoint + PredictPoint THEN t + 1 ELSE t

SendAlive(p) ==
    /\ \A q \in Proc \ {p} : [sender |-> p, dest |-> q] \notin Outbox[p]
    /\ Outbox' = [Outbox EXCEPT ![p] = {[sender |-> p, dest |-> q] : q \in Proc \ {p}}]
    /\ Clock' = [Clock EXCEPT ![p] = Bump(@)]
    /\ LastHeard' = [q \in Proc |-> IF q = p \/ q \in Suspicion[p]
                                   THEN LastHeard[q] ELSE @ + 1]
    /\ UNCHANGED <<Suspicion, AdaptiveTimeOuts>>

Predict(p) ==
    /\ \E q \in Proc \ {p} :
         /\ LastHeard[q] >= AdaptiveTimeOuts[q]
         /\ Suspicion' = [Suspicion EXCEPT ![p] = @ \cup {q}]
    /\ Clock' = [Clock EXCEPT ![p] = Bump(@)]
    /\ LastHeard' = [q \in Proc |-> IF q \in Suspicion[p] THEN @ ELSE @ + 1]
    /\ UNCHANGED <<AdaptiveTimeOuts, Outbox>>

ReceiveMsg(p, m) ==
    /\ m \in Outbox[m.sender]
    /\ Outbox' = [Outbox EXCEPT ![m.sender] = @ \ {m}]
    /\ LastHeard' = [LastHeard EXCEPT ![m.sender] = 0]
    /\ Suspicion' = [Suspicion EXCEPT ![p] = @ \ {m.sender}]
    /\ AdaptiveTimeOuts' = [AdaptiveTimeOuts EXCEPT
        ![m.sender] = IF m.sender \in Suspicion[p] THEN @ + 1 ELSE @]
    /\ Clock' = [Clock EXCEPT ![p] = Bump(@)]

Stall(p) ==
    /\ Outbox[p] = {}
    /\ LastHeard' = [LastHeard EXCEPT ![p] = IF @ > 0 THEN @ - 1 ELSE 0]
    /\ UNCHANGED <<Suspicion, AdaptiveTimeOuts, Clock, Outbox>>

WrapClock(p) ==
    /\ Clock[p] > SendPoint + PredictPoint + d0
    /\ Clock' = [Clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<Suspicion, AdaptiveTimeOuts, LastHeard, Outbox>>

\* The receive relation is a set of per-sender messages, so a receive
\* step is quantified over that set instead of being a deterministic pair.
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc, m \in Messages : ReceiveMsg(p, m)
    \/ \E p \in Proc : Stall(p)
    \/ \E p \in Proc : WrapClock(p)

Spec == Init /\ [][Next]_vars

====