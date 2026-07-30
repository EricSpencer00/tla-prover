---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Per-process state: suspicion list, per-peer adaptive timeout interval, per-peer
\* last-heard counter, local clock, and currently pending outgoing messages.
VARIABLES suspect, timeout, lastHeard, clock, pending

vars == <<suspect, timeout, lastHeard, clock, pending>>

Message == [frm: Proc, to: Proc]

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ pending \in [Proc -> SUBSET Message]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ pending = [p \in Proc |-> {}]

\* Send alive at multiples of SendPoint, provided it is not also a predict point.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ pending' = [pending EXCEPT ![p] = {[frm |-> p, to |-> q] : q \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF q \in pending[p] /\ lastHeard[p][q] < timeout[p][q]
                       THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspect, timeout>>

\* Make a suspicion decision at multiples of PredictPoint (never overlapping with SendAlive).
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] =
        @ \cup {q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, pending>>

\* Receive messages at all other times; receipt recovers from suspicion and
\* bumps the adaptive timeout when a suspect is observed alive again.
Receive(p, msgs) ==
  /\ \A m \in msgs : m.to = p
  /\ suspect' = [suspect EXCEPT ![p] = @ \ {[m.frm : m \in msgs]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF \E m \in msgs : m.frm = q THEN 0 ELSE @]]
  /\ timeout' = [timeout EXCEPT ![p] =
        [q \in Proc |-> IF \E m \in msgs : m.frm = q /\ q \in suspect[p]
                       THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] =
        IF @ + 1 > (SendPoint \cup PredictPoint \cup UNION {timeout[p][q] : q \in Proc})
        THEN 0 ELSE @ + 1]
  /\ UNCHANGED <<pending>>

Next ==
  /\ \E p \in Proc : SendAlive(p) \/ Predict(p)
  /\ \E p \in Proc, msgs \in SUBSET Messages : Receive(p, msgs)

Spec == Init /\ [][Next]_vars

====