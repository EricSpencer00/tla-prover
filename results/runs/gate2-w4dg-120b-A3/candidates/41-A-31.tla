---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

\* Type annotation, used for the invariant below.
Msg == [from: Proc, to: Proc]

\* Send and predict are mutually exclusive by construction (send interval and
\* predict interval are not multiples of each other); the clock therefore
\* deterministically identifies which operation is enabled at any moment.
TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspicion \subseteq [process: Proc, suspect: Proc]
    /\ outbox \subseteq Msg

Init ==
    /\ suspicion = {}
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = {}

SendAlive ==
    \E p \in Proc :
        /\ clock[p] % SendPoint = 0
        /\ clock[p] % PredictPoint # 0
        /\ outbox' = outbox \cup {[from |-> p, to |-> q] : q \in Proc}
        /\ clock' = [clock EXCEPT ![p] = @ + 1]
        /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1
                                      FOR q \in Proc : lastHeard[p][q] < timeout[p][q]]
        /\ UNCHANGED <<suspicion, timeout>>

Predict ==
    \E p \in Proc :
        /\ clock[p] % PredictPoint = 0
        /\ clock[p] % SendPoint # 0
        /\ suspicion' = suspicion \cup {[process |-> p, suspect |-> q] : q \in Proc
                                          : lastHeard[p][q] > timeout[p][q]}
        /\ clock' = [clock EXCEPT ![p] = @ + 1]
        /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1
                                      FOR q \in Proc : lastHeard[p][q] < timeout[p][q]]
        /\ UNCHANGED <<timeout, outbox>>

Receive ==
    \E p \in Proc :
        /\ clock[p] % SendPoint # 0
        /\ clock[p] % PredictPoint # 0
        /\ LET got == {m \in outbox : m.to = p}
               dOut == {m \in outbox : m.to = p /\ m.from \in suspicion}
               reset == [lastHeard[p] EXCEPT ![m.from] = 0
                                           FOR m \in got]
               clnsp == suspicion \ {[process |-> p, suspect |-> m.from] : m \in got}
               adjust == [timeout[p] EXCEPT ![q] = IF \E m \in dOut : m.from = q
                                                   THEN @ + 1 ELSE @]
               nclk == IF clock[p] > SendPoint /\ clock[p] > PredictPoint
                           /\ \A q \in Proc : clock[p] > timeout[p][q] THEN 0 ELSE clock[p] + 1
               oreset == [outbox EXCEPT ! = @ \ got]
           IN /\ suspicion' = clnsp
              /\ timeout' = adjust
              /\ lastHeard' = reset
              /\ clock' = [clock EXCEPT ![p] = nclk]
              /\ outbox' = oreset

Next == SendAlive \/ Predict \/ Receive

Spec == Init /\ [][Next]_vars

====