---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

(* This module implements the basic process actions from the description, *)
(* together with the safety invariants that a supervisory controller (not *)
(* part of the model) is expected to verify.                            *)

CONSTANTS
  Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint # PredictPoint

VARIABLES
  sus, timeout, lastH, clock, outbox

vars == <<sus, timeout, lastH, clock, outbox>>

TypeOK ==
  /\ \A p \in Proc : sus[p] \subseteq Proc
  /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
  /\ \A p \in Proc : lastH[p] \in [Proc -> Nat]
  /\ \A p \in Proc : outbox[p] \subseteq Messages

Init ==
  /\ sus = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastH = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ outbox[p] = {}
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.typ = "alive" /\ m.to \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastH' = [lastH EXCEPT ![p] = [q \in Proc |-> IF lastH[p][q] < timeout[p][q] THEN lastH[p][q] + 1 ELSE lastH[p][q]]]
  /\ UNCHANGED <<sus, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ sus' = [sus EXCEPT ![p] = sus[p] \cup {q \in Proc : lastH[p][q] > timeout[p][q]}]
  /\ lastH' = [lastH EXCEPT ![p] = [q \in Proc |-> IF lastH[p][q] < timeout[p][q] THEN lastH[p][q] + 1 ELSE lastH[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ outbox[p] # {}
  /\ \E m \in outbox[p] : lastH[p][m.to] > 0 /\ ~(\E q \in outbox[p] : q.to = m.to /\ q.typ = m.typ)
  /\ sus' = [sus EXCEPT ![p] = sus[p] \ {m.to : m \in outbox[p]}]
  /\ lastH' = [lastH EXCEPT ![p] = [q \in Proc |-> IF q \in {m.to : m \in outbox[p]} THEN 0 ELSE lastH[p][q]]]
  /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |-> IF q \in {m.to : m \in outbox[p]} /\ q \in sus[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint /\ \A q \in Proc : clock[p] + 1 > timeout[p][q] THEN 0 ELSE clock[p] + 1]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====