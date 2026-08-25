---- MODULE EPFailureDetector ----
EXTENDS Naturals, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES sus, timeout, lastHeard, clk, out

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ sus \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clk \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Messages]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
AliveMsg(p, q) == [type |-> "Alive", from |-> p, to |-> q]

MaxTimeout(p) ==
    IF Proc = {} THEN 0
    ELSE Max({ timeout[p][q] : q \in Proc \ {p} })

MaxThresh(p) == Max({ SendPoint, PredictPoint, MaxTimeout(p) })

NextClock(c, p) ==
    LET c1 == c + 1 IN
    IF c1 >= MaxThresh(p) THEN 0 ELSE c1

(*-----------------------------------------------------------------
  Actions for a single process p
-----------------------------------------------------------------*)
Send(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = { AliveMsg(p, q) : q \in Proc \ {p} }]
    /\ sus' = sus
    /\ timeout' = timeout
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1]
    /\ clk' = [clk EXCEPT ![p] = NextClock(clk[p], p)]

Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ sus' = [sus EXCEPT ![p] = sus[p] \cup
                 { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }]
    /\ timeout' = timeout
    /\ out' = [out EXCEPT ![p] = {}]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1]
    /\ clk' = [clk EXCEPT ![p] = NextClock(clk[p], p)]

Receive(p) ==
    /\ ~(clk[p] % SendPoint = 0 /\ clk[p] % PredictPoint # 0)
    /\ ~(clk[p] % PredictPoint = 0 /\ clk[p] % SendPoint # 0)
    /\ \E R \subseteq { m \in Messages : m.to = p } :
          /\ sus' = [sus EXCEPT ![p] =
                     sus[p] \ { q \in Proc :
                         \E m \in R : m.from = q } ]
          /\ timeout' = [timeout EXCEPT ![p][q] =
                           IF \E m \in R : m.from = q /\ q \in sus[p] THEN @ + 1 ELSE @ ]
          /\ out' = [out EXCEPT ![p] = {}]
          /\ lastHeard' = [lastHeard EXCEPT ![p][q] =
                             IF \E m \in R : m.from = q THEN 0 ELSE @ + 1]
          /\ clk' = [clk EXCEPT ![p] = NextClock(clk[p], p)]

(*-----------------------------------------------------------------
  Next relation: one process makes a step
-----------------------------------------------------------------*)
Next ==
    \E p \in Proc : \/ Send(p) \/ Predict(p) \/ Receive(p)

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ sus = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q # p THEN d0 ELSE 0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk = [p \in Proc |-> 0]
    /\ out = [p \in Proc |-> {}]

====