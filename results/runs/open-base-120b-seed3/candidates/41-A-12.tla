---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clk, suspicion, timeout, last, out

\* ----------------------------------------------------------------------
\* Type definitions and helper predicates
\* ----------------------------------------------------------------------
IsSend(p) == (clk[p] % SendPoint = 0) /\ (clk[p] % PredictPoint # 0)
IsPredict(p) == (clk[p] % PredictPoint = 0) /\ (clk[p] % SendPoint # 0)
IsOther(p) == ~IsSend(p) /\ ~IsPredict(p)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ clk = [p \in Proc |-> 0]
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ out = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send alive messages
\* ----------------------------------------------------------------------
Send(p) ==
  /\ IsSend(p)
  /\ out' = [out EXCEPT ![p] = @ \cup
               { [from |-> p, to |-> q, type |-> "alive"] :
                 q \in Proc \ {p} } ]
  /\ clk' = [clk EXCEPT ![p] = @ + 1]
  /\ last' = [last EXCEPT ![p][q] =
                IF last[p][q] < timeout[p][q] THEN @ + 1 ELSE @
                \* for every q \in Proc
              ]
  /\ UNCHANGED << suspicion, timeout >>

\* ----------------------------------------------------------------------
\* Predict crashes
\* ----------------------------------------------------------------------
Predict(p) ==
  /\ IsPredict(p)
  /\ suspicion' = [suspicion EXCEPT ![p] =
                     @ \cup { q \in Proc : last[p][q] > timeout[p][q] } ]
  /\ clk' = [clk EXCEPT ![p] = @ + 1]
  /\ last' = [last EXCEPT ![p][q] = @ + 1]
  /\ UNCHANGED << out, timeout >>

\* ----------------------------------------------------------------------
\* Receive messages
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ IsOther(p)
  LET msgs == { m \in UNION { out[r] : r \in Proc } :
                 m.to = p /\ m.type = "alive" }
      receivedFrom == { m.from : m \in msgs }
      originalSus == suspicion[p]
  IN
    /\ out' = out
    /\ clk' = [clk EXCEPT ![p] = @ + 1]
    /\ last' = [last EXCEPT ![p][q] = IF q \in receivedFrom THEN 0 ELSE @]
    /\ suspicion' = [suspicion EXCEPT ![p] = @ \ { q \in receivedFrom } ]
    /\ timeout' = [timeout EXCEPT ![p][q] =
                     IF q \in originalSus /\ q \in receivedFrom THEN @ + 1 ELSE @]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Send(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* State-variables tuple for the action operator
\* ----------------------------------------------------------------------
vars == << clk, suspicion, timeout, last, out >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ clk \in [Proc -> Nat]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ last \in [Proc -> [Proc -> Nat]]
  /\ out \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification (optional, not required by the cfg)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================