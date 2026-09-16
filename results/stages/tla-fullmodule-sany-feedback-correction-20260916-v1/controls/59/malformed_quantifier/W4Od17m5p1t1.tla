-------------------------------- MODULE W4Od17m5p1t1 --------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Routers, Pids, MaxVer
VARIABLES recVer, proposals, ballots, applied
vars == <<recVer, proposals, ballots, applied>>

OpenPids == { p.pid : p \in proposals }
BallotsFor(pid) == { b \in ballots : b.pid = pid }
Quorum(pid) == 2 * Cardinality(BallotsFor(pid)) > Cardinality(Routers)

Init ==
    /\ recVer = 0
    /\ proposals = {}
    /\ ballots = {}
    /\ applied = {}

Propose(pid) ==
    /\ recVer < MaxVer
    /\ pid \notin OpenPids
    /\ proposals' = proposals \union {[pid |-> pid, base |-> recVer]}
    /\ UNCHANGED <<recVer, ballots, applied>>

CastBallot(r, pid) ==
    /\ pid \in OpenPids
    /\ [pid |-> pid, voter |-> r] \notin ballots
    /\ ballots' = ballots \union {[pid |-> pid, voter |-> r]}
    /\ UNCHANGED <<recVer, proposals, applied>>

Commit(pid) ==
    /\ \E p \in proposals : p.pid = pid /\ p.base = recVer
    /\ recVer < MaxVer
    /\ Quorum(pid)
    /\ recVer' = recVer + 1
    /\ applied' = applied \union {pid}
    /\ proposals' = { p \in proposals : p.pid # pid }
    /\ ballots' = { b \in ballots : b.pid # pid }

Discard(pid) ==
    /\ \E p \in proposals : p.pid = pid /\ (p.base # recVer \/ recVer >= MaxVer)
    /\ proposals' = { p \in proposals : p.pid # pid }
    /\ ballots' = { b \in ballots : b.pid # pid }
    /\ UNCHANGED <<recVer, applied>>

Rollover ==
    /\ recVer >= MaxVer
    /\ recVer' = 0
    /\ proposals' = {}
    /\ ballots' = {}
    /\ applied' = {}

Next ==
    \/ \E pid \in Pids : Propose(pid)
    \/ \E r \in Routers, pid \in Pids : CastBallot(r, pid)
    \/ \E pid \in Pids : Commit(pid)
    \/ \E pid \in Pids : Discard(pid)
    \/ Rollover

Spec == Init /\ [][Next]_vars

BaseNeverAhead == \A \in proposals : p.base <= recVer
=============================================================================