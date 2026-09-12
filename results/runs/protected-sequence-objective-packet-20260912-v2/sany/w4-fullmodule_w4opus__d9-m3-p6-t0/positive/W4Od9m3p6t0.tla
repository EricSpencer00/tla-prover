------------------------------ MODULE W4Od9m3p6t0 ------------------------------
EXTENDS Naturals

CONSTANTS Controllers, MaxTerm

NoOne == "no_one"

VARIABLES term, leader, cstate, cterm, shedActive

vars == <<term, leader, cstate, cterm, shedActive>>

TypeOK ==
    /\ term \in 0..MaxTerm
    /\ leader \in Controllers \union {NoOne}
    /\ cstate \in [Controllers -> {"follower", "leader", "crashed"}]
    /\ cterm \in [Controllers -> 0..MaxTerm]
    /\ shedActive \in BOOLEAN

Init ==
    /\ term = 0
    /\ leader = NoOne
    /\ cstate = [c \in Controllers |-> "follower"]
    /\ cterm = [c \in Controllers |-> 0]
    /\ shedActive = FALSE

\* A live controller wins an election under a fresh, higher term and becomes the
\* leader. Any previous leader is thereby left stale (its term is now behind).
Elect(c) ==
    /\ cstate[c] # "crashed"
    /\ term < MaxTerm
    /\ term' = term + 1
    /\ leader' = c
    /\ cstate' = [cstate EXCEPT ![c] = "leader"]
    /\ cterm' = [cterm EXCEPT ![c] = term + 1]
    /\ UNCHANGED shedActive

\* Only a leader whose term is the current term may drive load shedding.
Shed(c) ==
    /\ cstate[c] = "leader"
    /\ cterm[c] = term
    /\ shedActive' = ~ shedActive
    /\ UNCHANGED <<term, leader, cstate, cterm>>

\* A single controller may crash silently. If it was the leader, the leader
\* pointer is cleared, triggering a later failover election.
Crash(c) ==
    /\ \A x \in Controllers : cstate[x] # "crashed"
    /\ cstate' = [cstate EXCEPT ![c] = "crashed"]
    /\ leader' = IF leader = c THEN NoOne ELSE leader
    /\ UNCHANGED <<term, cterm, shedActive>>

\* A crashed controller recovers as a follower.
Recover(c) ==
    /\ cstate[c] = "crashed"
    /\ cstate' = [cstate EXCEPT ![c] = "follower"]
    /\ UNCHANGED <<term, leader, cterm, shedActive>>

\* A stale leader (one still calling itself leader but on an old term) steps down.
StepDown(c) ==
    /\ cstate[c] = "leader"
    /\ cterm[c] # term
    /\ cstate' = [cstate EXCEPT ![c] = "follower"]
    /\ UNCHANGED <<term, leader, cterm, shedActive>>

Next ==
    \/ \E c \in Controllers : Elect(c)
    \/ \E c \in Controllers : Shed(c)
    \/ \E c \in Controllers : Crash(c)
    \/ \E c \in Controllers : Recover(c)
    \/ \E c \in Controllers : StepDown(c)

Spec == Init /\ [][Next]_vars

\* No action by an unauthorized or stale participant: whenever a leader is
\* recorded, that controller genuinely regards itself as leader and its term is the
\* current term -- so neither a deposed stale leader nor a crashed controller can
\* be the authority that drives shedding.
LeaderAuthorized ==
    (leader # NoOne) => (cstate[leader] = "leader" /\ cterm[leader] = term)

=============================================================================