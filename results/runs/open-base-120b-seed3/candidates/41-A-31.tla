---- MODULE EPFailureDetector ----
EXTENDS Naturals, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, timeout, last, suspect, out

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)

IsProc(p) == p \in Proc
OtherProcs(p) == Proc \ {p}

MaxThreshold(p) ==
  LET ts == { timeout[p][q] : q \in OtherProcs(p) } \cup {SendPoint, PredictPoint}
  IN IF ts = {} THEN 0 ELSE Max(ts)

IncClock(p) ==
  LET c == clock[p] + 1 IN
    IF c > MaxThreshold(p) THEN 0 ELSE c

IncLast(p, q) ==
  IF last[p][q] < timeout[p][q] THEN last[p][q] + 1 ELSE last[p][q]

(*-----------------------------------------------------------------
  Init
-----------------------------------------------------------------*)

Init ==
  /\ clock   = [p \in Proc |-> 0]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
  /\ last    = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ suspect = [p \in Proc |-> {}]
  /\ out     = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)

SendAlive(p) ==
  /\ IsProc(p)
  /\ (clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0)
  /\ out'    = [out EXCEPT ![p] = { [type |-> "Alive", src |-> p, dst |-> q] : q \in OtherProcs(p) }]
  /\ clock'  = [clock EXCEPT ![p] = IncClock(p)]
  /\ timeout' = timeout
  /\ last'   = [last EXCEPT ![p] = [q \in Proc |-> IncLast(p, q)]]
  /\ suspect' = suspect

Predict(p) ==
  /\ IsProc(p)
  /\ (clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0)
  /\ let newSus == { q \in OtherProcs(p) : last[p][q] > timeout[p][q] } in
        suspect' = [suspect EXCEPT ![p] = suspect[p] \cup newSus]
  /\ out'    = out
  /\ clock'  = [clock EXCEPT ![p] = IncClock(p)]
  /\ timeout' = timeout
  /\ last'   = [last EXCEPT ![p] = [q \in Proc |-> IncLast(p, q)]]

Receive(p) ==
  /\ IsProc(p)
  /\ (clock[p] % SendPoint # 0) /\ (clock[p] % PredictPoint # 0)
  /\ \E recv \subseteq OtherProcs(p) :
        /\ out'    = out
        /\ clock'  = [clock EXCEPT ![p] = IncClock(p)]
        /\ timeout' = [timeout EXCEPT ![p][q] =
                         IF q \in recv /\ q \in suspect[p] THEN timeout[p][q] + 1
                         ELSE timeout[p][q] ]
        /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ { q \in recv }]
        /\ last'   = [last EXCEPT ![p][q] =
                         IF q \in recv THEN 0
                         ELSE IncLast(p, q) ]

(*-----------------------------------------------------------------
  Next
-----------------------------------------------------------------*)

Next ==
  \E p \in Proc : \/ SendAlive(p) \/ Predict(p) \/ Receive(p)

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)

TypeOK ==
  /\ clock   \in [Proc -> Nat]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ last    \in [Proc -> [Proc -> Nat]]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ out     \in [Proc -> SUBSET Messages]

(*-----------------------------------------------------------------
  Specification (optional)
-----------------------------------------------------------------*)

Spec == Init /\ [][Next]_<<clock, timeout, last, suspect, out>>

====