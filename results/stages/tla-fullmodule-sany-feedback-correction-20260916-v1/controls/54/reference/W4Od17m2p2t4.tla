---- MODULE W4Od17m2p2t4 ----
EXTENDS Naturals

CONSTANTS Zone, RM, Total, MaxCap, NoMove, Home

ASSUME NoMove \notin (Zone \X Zone)

VARIABLES bags, vote, pending, cap
vars == <<bags, vote, pending, cap>>

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET z == CHOOSE y \in S : TRUE IN bags[z] + SumOf(S \ {z})

Init ==
  /\ bags = [z \in Zone |-> IF z = Home THEN Total ELSE 0]
  /\ vote = [r \in RM |-> "none"]
  /\ pending = NoMove
  /\ cap = [z \in Zone |-> Total]

Propose(s, d) ==
  /\ pending = NoMove
  /\ s # d
  /\ pending' = <<s, d>>
  /\ vote' = [r \in RM |-> "none"]
  /\ UNCHANGED <<bags, cap>>

Prepare(r) ==
  /\ pending # NoMove
  /\ vote[r] = "none"
  /\ vote' = [vote EXCEPT ![r] = "yes"]
  /\ UNCHANGED <<bags, pending, cap>>

Commit ==
  /\ pending # NoMove
  /\ \A r \in RM : vote[r] = "yes"
  /\ LET s == pending[1]
         d == pending[2] IN
       /\ bags[s] > 0
       /\ bags[d] < cap[d]
       /\ bags' = [bags EXCEPT ![s] = @ - 1, ![d] = @ + 1]
  /\ pending' = NoMove
  /\ UNCHANGED <<vote, cap>>

Abort ==
  /\ pending # NoMove
  /\ pending' = NoMove
  /\ UNCHANGED <<bags, vote, cap>>

Resize(z, n) ==
  /\ n \in 1..MaxCap
  /\ n >= bags[z]
  /\ cap' = [cap EXCEPT ![z] = n]
  /\ UNCHANGED <<bags, vote, pending>>

Idle == UNCHANGED vars

Next ==
  \/ Idle
  \/ \E s, d \in Zone : Propose(s, d)
  \/ \E r \in RM : Prepare(r)
  \/ Commit
  \/ Abort
  \/ \E z \in Zone, n \in 1..MaxCap : Resize(z, n)

Spec == Init /\ [][Next]_vars

BagConservation == SumOf(Zone) = Total
====