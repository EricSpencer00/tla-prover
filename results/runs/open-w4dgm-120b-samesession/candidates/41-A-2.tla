---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* A message records its originator so the receiver can tell which process's
\* timeout interval to mark as having been satisfied.
Message == [origin : Proc]

VARIABLES suspect, timeout, heard, clock, outgoing

vars == <<suspect, timeout, heard, clock, outgoing>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ heard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outgoing \in [Proc -> SUBSET Message]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ heard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

\* A fine-grained bound: a process may send only when its own clock is not
\* aligned with the prediction epoch, so send and predict can never fire together.
SendAlive(p) ==
    /\ ~ \E q \in Proc : q # p /\ clock[p] % SendPoint = 0
    /\ \A q \in Proc : q # p => outgoing' = [outgoing EXCEPT ![p] = @ \cup {[origin |-> q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ heard' = [heard EXCEPT ![p] = [q \in Proc |-> IF q = p \/ heard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ ~ \E q \in Proc : q # p /\ clock[p] % PredictPoint = 0
    /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc : q # p /\ heard[p][q] > timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ heard' = [heard EXCEPT ![p] = [q \in Proc |-> IF q = p \/ heard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
    /\ \E m \in outgoing[p] :
         /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.origin}]
         /\ heard' = [heard EXCEPT ![p] = [@ EXCEPT ![m.origin] = 0]]
         /\ timeout' = [timeout EXCEPT ![p][m.origin] = IF m.origin \in suspect[p] THEN @ + 1 ELSE @]
         /\ outgoing' = [outgoing EXCEPT ![p] = @ \ {m}]
    /\ UNCHANGED clock

\* The clock rolls over once it has passed every active threshold, keeping the
\* reachable state space finite without ever disabling an action.
ResetClock(p) ==
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : q # p => clock[p] > timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, heard, outgoing>>

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p) \/ ResetClock(p)

Spec == Init /\ [][Next]_vars

====