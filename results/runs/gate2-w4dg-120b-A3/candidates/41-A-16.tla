---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc, d0, SendPoint, PredictPoint, Messages

RECURSIVE MinCard(_, _)
MinCard(k, S) ==
    IF S = {} THEN k
    ELSE LET m == CHOOSE x \in S : TRUE IN Min(m, MinCard(k, S \ {m}))

VARIABLES suspect, timeout, lastHeard, clock, pending

vars == <<suspect, timeout, lastHeard, clock, pending>>

\* A message targets one receiver and names the sender it is carrying.
Msg == [to : Proc, from : Proc]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ pending = [p \in Proc |-> {}]

Send(p) ==
    /\ p \in Proc
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ pending' = [pending EXCEPT ![p] =
                      { [to |-> q, from |-> p] : q \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ p \in Proc
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] =
                    { q \in Proc : clock[p] - lastHeard[p][q] > timeout[p] } \cup suspect[p]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<timeout, pending>>

Receive(p, mset) ==
    /\ p \in Proc
    /\ mset # {}
    /\ mset \subseteq pending[p]
    /\ pending' = [pending EXCEPT ![p] = pending[p] \ mset]
    /\ suspect' = [suspect EXCEPT ![p] =
                    suspect[p] \ { m.from : m \in mset }]
    /\ timeout' = [timeout EXCEPT ![p] =
                    [q \in Proc |-> IF \E m \in mset : m.from = q THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF \E m \in mset : m.from = q THEN 0 ELSE lastHeard[p][q]]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]

ClockReset(p) ==
    /\ p \in Proc
    /\ clock[p] > MinCard(1, {SendPoint, PredictPoint} \cup {timeout[p][q] : q \in Proc})
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, pending>>

Next ==
    \/ \E p \in Proc : Send(p) \/ Predict(p) \/ ClockReset(p)
    \/ \E p \in Proc, mset \in SUBSET Messages : Receive(p, mset)

Spec ==
    /\ Init
    /\ [][Next]_vars

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ pending \in [Proc -> SUBSET Messages]

====