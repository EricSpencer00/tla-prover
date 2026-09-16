-------------------------- MODULE W4Od14m2p2t1 --------------------------
EXTENDS Naturals
CONSTANTS Drones, Budget

VARIABLES phase, vote, tokens, src, dst

vars == <<phase, vote, tokens, src, dst>>

NoDrone == "none"

RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN tokens[x] + SumOver(S \ {x})

AllYes == \A d \in Drones : vote[d] = "yes"
SomeNo == \E d \in Drones : vote[d] = "no"

Init ==
    /\ phase = "idle"
    /\ vote = [d \in Drones |-> "none"]
    /\ tokens = [d \in Drones |-> IF d = CHOOSE x \in Drones : TRUE THEN Budget ELSE 0]
    /\ src = NoDrone
    /\ dst = NoDrone

Begin(s, t) ==
    /\ phase = "idle"
    /\ s # t
    /\ tokens[s] > 0
    /\ phase' = "voting"
    /\ vote' = [d \in Drones |-> "none"]
    /\ src' = s
    /\ dst' = t
    /\ UNCHANGED tokens

Vote(d, v) ==
    /\ phase = "voting"
    /\ vote[d] = "none"
    /\ v \in {"yes", "no"}
    /\ vote' = [vote EXCEPT ![d] = v]
    /\ UNCHANGED <<phase, tokens, src, dst>>

Commit ==
    /\ phase = "voting"
    /\ AllYes
    /\ tokens' = [tokens EXCEPT ![src] = @ - 1, ![dst] = @ + 1]
    /\ phase' = "committed"
    /\ UNCHANGED <<vote, src, dst>>

Abort ==
    /\ phase = "voting"
    /\ SomeNo
    /\ phase' = "aborted"
    /\ UNCHANGED <<vote, tokens, src, dst>>

Reset ==
    /\ phase \in {"committed", "aborted"}
    /\ phase' = "idle"
    /\ vote' = [d \in Drones |-> "none"]
    /\ src' = NoDrone
    /\ dst' = NoDrone
    /\ UNCHANGED tokens

Next ==
    \/ \E s, t \in Drones : Begin(s, t)
    \/ \E d \in Drones, v \in {"yes", "no"} : Vote(d, v)
    \/ Commit
    \/ Abort
    \/ Reset

Spec == Init /\ [][Next]_vars

TokensConserved == SumOver(Drones) = Budget
=============================================================================