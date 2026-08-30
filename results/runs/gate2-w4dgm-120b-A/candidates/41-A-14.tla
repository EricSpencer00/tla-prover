---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Alive messages: who sent them and who they are addressed to.
Message == [from: Proc, to: Proc]

VARIABLES suspect, timeout, notHeardFor, clock, outgoing

vars == <<suspect, timeout, notHeardFor, clock, outgoing>>

\* A process is never timed out on: it is always considered recently heard
\* from, keeping its outgoing set stably nonempty once it sends.
TimedOut(p, q) == p # q /\ notHeardFor[p][q] > timeout[p][q]

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ notHeardFor \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outgoing \in [Proc -> SUBSET Message]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ notHeardFor = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] =
        {m \in outgoing[p] : m.to # p} \cup {[from |-> p, to |-> q] : q \in Proc}
  ]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ notHeardFor' = [q \in Proc |->
        IF TimedOut(p, q) THEN notHeardFor[p][q] + 1 ELSE notHeardFor[p][q]
  ]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p]
        \cup {q \in Proc : notHeardFor[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ notHeardFor' = [q \in Proc |->
        IF TimedOut(p, q) THEN notHeardFor[p][q] + 1 ELSE notHeardFor[p][q]
  ]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p, m) ==
  /\ m \in outgoing[p]
  /\ outgoing' = [outgoing EXCEPT ![p] = outgoing[p] \ {m}]
  /\ notHeardFor' = [notHeardFor EXCEPT ![p][m.from] = 0]
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
  /\ timeout' = [timeout EXCEPT ![p][m.from] = IF m.from \in suspect[p]
        THEN timeout[p][m.from] + 1 ELSE timeout[p][m.from]]
  /\ UNCHANGED <<clock>>

ResetClock(p) ==
  /\ clock[p] >= SendPoint + PredictPoint
      + (IF d0 = 0 THEN 1 ELSE d0 + 2)
      + (IF SendPoint > PredictPoint THEN SendPoint ELSE PredictPoint)
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspect, timeout, notHeardFor, outgoing>>

Recv(p) == \E m \in Messages : Receive(p, m)

Next ==
  \E p \in Proc :
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Recv(p)
    \/ ResetClock(p)

Spec == Init /\ [][Next]_vars

====