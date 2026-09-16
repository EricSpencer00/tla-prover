---------------------------- MODULE W4Od1m2p2t0 ----------------------------
EXTENDS Naturals
Total   == 4
Towers  == {"t1", "t2"}

VARIABLES free, pending, allocated, votes, alive

TypeInv ==
    /\ free \in 0..Total
    /\ pending \in 0..Total
    /\ allocated \in 0..Total
    /\ votes \subseteq Towers
    /\ alive \subseteq Towers

Init ==
    /\ free = Total
    /\ pending = 0
    /\ allocated = 0
    /\ votes = {}
    /\ alive = Towers

Propose ==
    /\ pending = 0
    /\ free > 0
    /\ free' = free - 1
    /\ pending' = 1
    /\ votes' = {}
    /\ UNCHANGED <<allocated, alive>>

Vote(t) ==
    /\ pending = 1
    /\ t \in alive
    /\ votes' = votes \cup {t}
    /\ UNCHANGED <<free, pending, allocated, alive>>

Commit ==
    /\ pending = 1
    /\ votes = alive
    /\ alive = Towers
    /\ pending' = 0
    /\ allocated' = allocated + 1
    /\ votes' = {}
    /\ UNCHANGED <<free, alive>>

Abort ==
    /\ pending = 1
    /\ pending' = 0
    /\ free' = free + 1
    /\ votes' = {}
    /\ UNCHANGED <<allocated, alive>>

Crash(t) ==
    /\ t \in alive
    /\ alive' = alive \ {t}
    /\ UNCHANGED <<free, pending, allocated, votes>>

Release ==
    /\ allocated > 0
    /\ allocated' = allocated - 1
    /\ free' = free + 1
    /\ UNCHANGED <<pending, votes, alive>>

Next ==
    \/ Propose \/ Commit \/ Abort \/ Release
    \/ \E t \in Towers : Vote(t) \/ Crash(t)

SlotsConserved == free + pending + allocated = Total

vars == <<free, pending, allocated, votes, alive>>
Spec == Init /\ [][Next]_vars
===