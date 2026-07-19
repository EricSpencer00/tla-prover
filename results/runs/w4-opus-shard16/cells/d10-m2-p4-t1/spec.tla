-------------------------- MODULE W4Od10m2p4t1 --------------------------
EXTENDS Naturals

CONSTANTS Trains, Signals, Cap

VARIABLES
    occupancy,  \* number of trains inside the interlocking
    txn,        \* txn[tr] : "idle" | "preparing" | "in" | "out"
    votes       \* votes[tr] : set of signals that voted yes for train tr

vars == << occupancy, txn, votes >>

TypeOK ==
    /\ occupancy \in 0..Cap
    /\ txn \in [Trains -> {"idle", "preparing", "in", "out"}]
    /\ votes \in [Trains -> SUBSET Signals]

Init ==
    /\ occupancy = 0
    /\ txn = [tr \in Trains |-> "idle"]
    /\ votes = [tr \in Trains |-> {}]

\* A train opens a movement-authority request.
StartReq(tr) ==
    /\ txn[tr] = "idle"
    /\ txn' = [txn EXCEPT ![tr] = "preparing"]
    /\ votes' = [votes EXCEPT ![tr] = {}]
    /\ UNCHANGED occupancy

\* A guarding signal votes yes; votes may be recorded in any order.
Vote(tr, s) ==
    /\ txn[tr] = "preparing"
    /\ s \notin votes[tr]
    /\ votes' = [votes EXCEPT ![tr] = @ \cup {s}]
    /\ UNCHANGED << occupancy, txn >>

\* Commit and enter only with unanimous votes and remaining room.
CommitEnter(tr) ==
    /\ txn[tr] = "preparing"
    /\ votes[tr] = Signals
    /\ occupancy < Cap
    /\ occupancy' = occupancy + 1
    /\ txn' = [txn EXCEPT ![tr] = "in"]
    /\ UNCHANGED votes

\* A request that cannot complete is aborted.
Abort(tr) ==
    /\ txn[tr] = "preparing"
    /\ txn' = [txn EXCEPT ![tr] = "idle"]
    /\ votes' = [votes EXCEPT ![tr] = {}]
    /\ UNCHANGED occupancy

\* A train leaves the interlocking.
Exit(tr) ==
    /\ txn[tr] = "in"
    /\ occupancy > 0
    /\ occupancy' = occupancy - 1
    /\ txn' = [txn EXCEPT ![tr] = "out"]
    /\ UNCHANGED votes

\* The train's slot is recycled for a future request.
Recycle(tr) ==
    /\ txn[tr] = "out"
    /\ txn' = [txn EXCEPT ![tr] = "idle"]
    /\ UNCHANGED << occupancy, votes >>

Next ==
    \/ \E tr \in Trains : StartReq(tr)
    \/ \E tr \in Trains, s \in Signals : Vote(tr, s)
    \/ \E tr \in Trains : CommitEnter(tr)
    \/ \E tr \in Trains : Abort(tr)
    \/ \E tr \in Trains : Exit(tr)
    \/ \E tr \in Trains : Recycle(tr)

Spec == Init /\ [][Next]_vars

\* Bounded capacity: the interlocking is never over-occupied.
WithinCapacity == occupancy <= Cap

=============================================================================
