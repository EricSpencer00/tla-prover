---- MODULE W4Od19m9p1t0 ----
EXTENDS Integers
CONSTANTS Patrons, MaxEpoch
VARIABLES epoch, ledger, stamp, alive
vars == <<epoch, ledger, stamp, alive>>

TypeState ==
    /\ epoch \in 0..MaxEpoch
    /\ ledger \in 0..5
    /\ stamp \in [Patrons -> 0..MaxEpoch \cup {-1}]
    /\ alive \in [Patrons -> BOOLEAN]

Init ==
    /\ epoch = 0
    /\ ledger = 0
    /\ stamp = [p \in Patrons |-> -1]
    /\ alive = [p \in Patrons |-> TRUE]

Sync(p) ==
    /\ alive[p]
    /\ stamp[p] = -1
    /\ stamp' = [stamp EXCEPT ![p] = epoch]
    /\ UNCHANGED <<epoch, ledger, alive>>

Commit(p) ==
    /\ alive[p]
    /\ stamp[p] = epoch
    /\ ledger < 5
    /\ ledger' = ledger + 1
    /\ stamp' = [stamp EXCEPT ![p] = -1]
    /\ UNCHANGED <<epoch, alive>>

RejectStale(p) ==
    /\ stamp[p] # -1
    /\ stamp[p] # epoch
    /\ stamp' = [stamp EXCEPT ![p] = -1]
    /\ UNCHANGED <<epoch, ledger, alive>>

Crash(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<epoch, ledger, stamp>>

Rotate ==
    /\ epoch < MaxEpoch
    /\ epoch' = epoch + 1
    /\ UNCHANGED <<ledger, stamp, alive>>

Next ==
    \/ \E p \in Patrons : Sync(p) \/ Commit(p) \/ RejectStale(p) \/ Crash(p)
    \/ Rotate

Spec == Init /\ [][Next]_vars

LedgerMonotone ==
    /\ ledger >= 0
    /\ (\A p \in Patrons : stamp[p] # -1 => stamp[p] <= epoch)
====