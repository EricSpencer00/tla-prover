------------------------- MODULE W4Od13m7p1t4 -------------------------
(* Vending-machine network with a shared restock record held in a
   compare-and-swap register.  Each restock reads the record's current value
   as its expected value, then does a CAS that writes value+1 only if the
   register still holds that expected value; a CAS whose expectation no longer
   matches has been raced and is discarded, so it can never overwrite and lose
   a concurrent restock.  The shelf capacity can change at runtime but never
   drops below the current record.  We count accepted restocks; safety: the
   record equals the number of accepted restocks, so no restock is lost. *)
EXTENDS Naturals

MaxCap == 3

VARIABLES record, inflight, numUpdates, capacity

TypeInv ==
    /\ record \in 0..MaxCap
    /\ inflight \subseteq [expect : 0..MaxCap]
    /\ numUpdates \in 0..MaxCap
    /\ capacity \in 1..MaxCap

Init ==
    /\ record = 0
    /\ inflight = {}
    /\ numUpdates = 0
    /\ capacity = 1

BeginCAS ==
    /\ inflight' = inflight \union {[expect | -> record]}
    /\ UNCHANGED <<record, numUpdates, capacity>>

CommitCAS(op) ==
    /\ op \in inflight
    /\ op.expect = record
    /\ record < capacity
    /\ record' = op.expect + 1
    /\ numUpdates' = numUpdates + 1
    /\ inflight' = inflight \ {op}
    /\ UNCHANGED capacity

FailCAS(op) ==
    /\ op \in inflight
    /\ op.expect # record
    /\ inflight' = inflight \ {op}
    /\ UNCHANGED <<record, numUpdates, capacity>>

Resize ==
    /\ \E c \in 1..MaxCap :
        /\ c >= record
        /\ capacity' = c
    /\ UNCHANGED <<record, inflight, numUpdates>>

Next ==
    \/ BeginCAS
    \/ \E op \in inflight : CommitCAS(op)
    \/ \E op \in inflight : FailCAS(op)
    \/ Resize

NoLostUpdates == record = numUpdates

vars == <<record, inflight, numUpdates, capacity>>
Spec == Init /\ [][Next]_vars
=======================================================================