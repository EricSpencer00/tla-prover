---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

(* ------------------------------------------------------------------- *)
(* Helper definitions *)
Other(p) == Proc \ {p}

Alive(p, q) == [type |-> "Alive", src |-> p, dst |-> q]

(* ------------------------------------------------------------------- *)
(* Variables *)
VARIABLES clock, suspicion, timeout, lastHeard, out

(* ------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ out \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc: suspicion[p] \subseteq Other(p)
    /\ \A p \in Proc: \A q \in Other(p): timeout[p][q] >= 0
    /\ \A p \in Proc: \A q \in Other(p): lastHeard[p][q] >= 0

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Other(p) |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Other(p) |-> 0]]
    /\ out = [p \in Proc |-> {}]

(* ------------------------------------------------------------------- *)
(* Helper to increment counters that have not yet timed out *)
IncCounters(p) ==
    [q \in Other(p) |-> IF lastHeard[p][q] < timeout[p][q]
                         THEN lastHeard[p][q] + 1
                         ELSE lastHeard[p][q]]

(* ------------------------------------------------------------------- *)
(* Actions *)

Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = out[p] \cup { Alive(p, q) : q \in Other(p) }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncCounters(p)]
    /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ let newSus == { q \in Other(p) : lastHeard[p][q] > timeout[p][q] } in
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncCounters(p)]
    /\ UNCHANGED << out, timeout >>

Receive(p) ==
    \E recv \in SUBSET Other(p) :
        /\ lastHeard' = [lastHeard EXCEPT ![p] =
               [q \in Other(p) |-> IF q \in recv THEN 0
                                      ELSE lastHeard[p][q] + 1]]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ recv]
        /\ timeout' = [timeout EXCEPT ![p] =
               [q \in Other(p) |-> IF q \in recv /\ q \in suspicion[p]
                                      THEN timeout[p][q] + 1
                                      ELSE timeout[p][q]]]
        /\ LET maxThresh == Max({SendPoint, PredictPoint}
                               \cup { timeout[p][q] : q \in Other(p) })
           IN
              clock' = [clock EXCEPT ![p] =
                         IF clock[p] + 1 > maxThresh THEN 0 ELSE clock[p] + 1]
        /\ out' = out

(* ------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \/ \E p \in Proc : Send(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

(* ------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<clock, suspicion, timeout, lastHeard, out>>

====