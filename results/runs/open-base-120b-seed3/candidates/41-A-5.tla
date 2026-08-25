---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

(*--------------------------------------------------------------------
  CONSTANTS
--------------------------------------------------------------------*)
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of possible messages (alive messages)

(*--------------------------------------------------------------------
  VARIABLES
--------------------------------------------------------------------*)
VARIABLES
    clk,          \* [p \in Proc |-> local clock of p]
    suspicion,    \* [p \in Proc |-> SUBSET Proc]   (processes p suspects)
    timeout,      \* [p \in Proc |-> [q \in Proc |-> Nat]] (adaptive timeout)
    last,         \* [p \in Proc |-> [q \in Proc |-> Nat]] (ticks since last alive from q)
    outbox        \* [p \in Proc |-> SUBSET Messages]   (messages p will send)

vars == << clk, suspicion, timeout, last, outbox >>

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
AliveMsg(p,q) == [type |-> "alive", from |-> p, to |-> q]

AllAliveMsgs == { AliveMsg(p,q) : p \in Proc, q \in Proc, p # q }

Init ==
    /\ clk = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ outbox = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Actions for a single process p
--------------------------------------------------------------------*)
SendAlive(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { AliveMsg(p,q) : q \in Proc, q # p }]
    /\ clk' = [clk EXCEPT ![p] = 
                IF (clk[p] + 1) > SendPoint 
                   /\ (clk[p] + 1) > PredictPoint 
                   /\ \A q \in Proc : (clk[p] + 1) > timeout[p][q]
               THEN 0 
               ELSE clk[p] + 1]
    /\ last' = [last EXCEPT ![p] = 
                [q \in Proc |-> 
                    IF last[p][q] < timeout[p][q] 
                    THEN last[p][q] + 1 
                    ELSE last[p][q]]]
    /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = 
          suspicion[p] \cup { q \in Proc : q # p /\ last[p][q] > timeout[p][q] }]
    /\ clk' = [clk EXCEPT ![p] = 
                IF (clk[p] + 1) > SendPoint 
                   /\ (clk[p] + 1) > PredictPoint 
                   /\ \A q \in Proc : (clk[p] + 1) > timeout[p][q]
               THEN 0 
               ELSE clk[p] + 1]
    /\ last' = [last EXCEPT ![p] = 
                [q \in Proc |-> 
                    IF last[p][q] < timeout[p][q] 
                    THEN last[p][q] + 1 
                    ELSE last[p][q]]]
    /\ UNCHANGED << outbox, timeout >>

Receive(p) ==
    /\ ~(clk[p] % SendPoint = 0 /\ clk[p] % PredictPoint # 0)
    /\ ~(clk[p] % PredictPoint = 0 /\ clk[p] % SendPoint # 0)
    /\ \* Determine which alive messages addressed to p exist in other outboxes
       let received == { q \in Proc : q # p /\ 
                         \E m \in outbox[q] : m.type = "alive" /\ m.to = p } in
    /\ clk' = [clk EXCEPT ![p] = 
                IF (clk[p] + 1) > SendPoint 
                   /\ (clk[p] + 1) > PredictPoint 
                   /\ \A q \in Proc : (clk[p] + 1) > timeout[p][q]
               THEN 0 
               ELSE clk[p] + 1]
    /\ last' = [last EXCEPT ![p] = 
                [q \in Proc |-> 
                    IF q \in received 
                    THEN 0 
                    ELSE IF last[p][q] < timeout[p][q] 
                         THEN last[p][q] + 1 
                         ELSE last[p][q]]]
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ { q \in received }]
    /\ timeout' = [timeout EXCEPT ![p] = 
                [q \in Proc |-> 
                    IF q \in received /\ q \in suspicion[p] 
                    THEN timeout[p][q] + 1 
                    ELSE timeout[p][q]]]
    /\ outbox' = outbox
    /\ UNCHANGED << >>

(*--------------------------------------------------------------------
  Next relation
--------------------------------------------------------------------*)
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ clk \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ outbox \in [Proc -> SUBSET Messages]

(*--------------------------------------------------------------------
  Assumptions about constants
--------------------------------------------------------------------*)
ASSUME SendPoint > 0
ASSUME PredictPoint > 0
ASSUME SendPoint % PredictPoint # 0
ASSUME PredictPoint % SendPoint # 0
ASSUME d0 > 0
ASSUME Messages = AllAliveMsgs

(*--------------------------------------------------------------------
  Theorems (optional)
--------------------------------------------------------------------*)
THEOREM Spec => []TypeOK

=============================================================================