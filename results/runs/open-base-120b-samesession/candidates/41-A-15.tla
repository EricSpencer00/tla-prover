---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES susp, timeout, last, clk, out

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ susp \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ clk \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Messages]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
INIT ==
    /\ susp = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk = [p \in Proc |-> 0]
    /\ out = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Send alive messages
-----------------------------------------------------------------*)
SendAlive(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = { [type |-> "alive", src |-> p, dst |-> q] : q \in Proc \ {p} }]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ last' = [last EXCEPT ![p] =
                 [q \in Proc |-> IF q = p THEN 0
                               ELSE IF last[p][q] < timeout[p][q] THEN last[p][q] + 1
                               ELSE last[p][q]]]
    /\ susp' = susp
    /\ timeout' = timeout

(*-----------------------------------------------------------------
  Predict failures
-----------------------------------------------------------------*)
Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ susp' = [susp EXCEPT ![p] = susp[p] \cup
                { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
    /\ last' = [last EXCEPT ![p] =
                 [q \in Proc |-> IF q = p THEN 0 ELSE last[p][q] + 1]]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ out' = out
    /\ timeout' = timeout

(*-----------------------------------------------------------------
  Receive alive messages (or none)
-----------------------------------------------------------------*)
Receive(p) ==
    \/ \E q \in Proc :
          /\ [type |-> "alive", src |-> q, dst |-> p] \in Messages
          /\ last' = [last EXCEPT ![p][q] = 0]
          /\ susp' = [susp EXCEPT ![p] = susp[p] \ {q}]
          /\ timeout' = [timeout EXCEPT ![p][q] =
                         IF q \in susp[p] THEN timeout[p][q] + 1
                         ELSE timeout[p][q]]
          /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
          /\ out' = out
    \/ (* no message received *)
       /\ last' = last
       /\ susp' = susp
       /\ timeout' = timeout
       /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
       /\ out' = out

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
NEXT ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
SPECIFICATION ==
    INIT /\ [][NEXT]_<<susp, timeout, last, clk, out>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
INVARIANTS ==
    TypeOK

(*-----------------------------------------------------------------
  Additional properties (none required)
-----------------------------------------------------------------*)
PROPERTIES == TRUE

====