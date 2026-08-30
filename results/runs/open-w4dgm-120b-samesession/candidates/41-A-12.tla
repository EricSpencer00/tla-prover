---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, sendBuf
vars == <<suspicion, timeout, lastHeard, clock, sendBuf>>

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> 0 .. d0]]
  /\ timeout \in [Proc -> [Proc -> 1 .. d0]]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ sendBuf \subseteq Messages

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ sendBuf = {}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ sendBuf' = {m \in sendBuf : m.from # p} \cup
                 {[from |-> p, to |-> q] : q \in Proc \ {p}}
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF q \in suspicion[p] /\ @ [q] < timeout[p][q] THEN @ [q] + 1 ELSE @ [q]]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] =
        {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF q \in suspicion[p] /\ @ [q] < timeout[p][q] THEN @ [q] + 1 ELSE @ [q]]]
  /\ UNCHANGED <<timeout, sendBuf>>

Receive(p) ==
  /\ (clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0)
  /\ \E m \in sendBuf :
        /\ m.to = p
        /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
        /\ suspicion' = [suspicion EXCEPT ![p] = @ \ {m.from}]
        /\ timeout' = [timeout EXCEPT ![p][m.from] =
              IF m.from \in suspicion[p] THEN IF @ < d0 THEN @ + 1 ELSE @ ELSE @]
        /\ sendBuf' = sendBuf \ {m}
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= d0 \/ clock[p] >= SendPoint \/ clock[p] >= PredictPoint
                                 THEN 0 ELSE @ + 1]

Next ==
  \/ \E p \in Proc: SendAlive(p)
  \/ \E p \in Proc: Predict(p)
  \/ \E p \in Proc: Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc: SF_vars(Receive(p))

SpecOK == Spec /\ TypeOK
====