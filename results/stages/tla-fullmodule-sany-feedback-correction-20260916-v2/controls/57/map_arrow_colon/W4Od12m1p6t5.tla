---- MODULE W4Od12m1p6t5 ----
EXTENDS Integers
CONSTANTS CAP, MAXGEN
ASSUME CAP \in Nat /\ MAXGEN \in Nat

Trackers == {"b1", "b2", "b3"}
NextR(t) == CASE t = "b1" -> "b2"
              [] t = "b2" -> "b3"
              [] OTHER    -> "b1"

VARIABLES tokenHolder, tokenGen, phase, usedGen, stock
vars == <<tokenHolder, tokenGen, phase, usedGen, stock>>

Init == /\ tokenHolder = "b1"
        /\ tokenGen = 0
        /\ phase = [t \in Trackers : "idle"]
        /\ usedGen = [t \in Trackers |-> -1]
        /\ stock = 0

Pass(t) == /\ tokenHolder = t
           /\ phase[t] = "idle"
           /\ tokenHolder' = NextR(t)
           /\ UNCHANGED <<tokenGen, phase, usedGen, stock>>

Arm(t) == /\ tokenHolder = t
          /\ phase[t] = "idle"
          /\ phase' = [phase EXCEPT ![t] = "armed"]
          /\ usedGen' = [usedGen EXCEPT ![t] = tokenGen]
          /\ UNCHANGED <<tokenHolder, tokenGen, stock>>

Write(t) == /\ tokenHolder = t
            /\ phase[t] = "armed"
            /\ usedGen[t] = tokenGen
            /\ stock < CAP
            /\ phase' = [phase EXCEPT ![t] = "writing"]
            /\ stock' = stock + 1
            /\ UNCHANGED <<tokenHolder, tokenGen, usedGen>>

Finish(t) == /\ phase[t] = "writing"
             /\ phase' = [phase EXCEPT ![t] = "idle"]
             /\ usedGen' = [usedGen EXCEPT ![t] = -1]
             /\ UNCHANGED <<tokenHolder, tokenGen, stock>>

DropStale(t) == /\ phase[t] \in {"armed", "writing"}
                /\ (tokenHolder # t \/ usedGen[t] # tokenGen)
                /\ phase' = [phase EXCEPT ![t] = "idle"]
                /\ usedGen' = [usedGen EXCEPT ![t] = -1]
                /\ UNCHANGED <<tokenHolder, tokenGen, stock>>

AdminRevoke == /\ tokenGen' = IF tokenGen < MAXGEN THEN tokenGen + 1 ELSE tokenGen
               /\ phase' = [t \in Trackers |-> "idle"]
               /\ usedGen' = [t \in Trackers |-> -1]
               /\ \E e \in Trackers : tokenHolder' = e
               /\ UNCHANGED stock

Next == \/ \E t \in Trackers : Pass(t) \/ Arm(t) \/ Write(t) \/ Finish(t) \/ DropStale(t)
        \/ AdminRevoke

Spec == Init /\ [][Next]_vars

NoUnauthorizedWriter ==
    \A t \in Trackers :
        phase[t] \in {"armed", "writing"} =>
            (tokenHolder = t /\ usedGen[t] = tokenGen)
====