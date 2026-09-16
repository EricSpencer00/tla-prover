------------------------------ MODULE W4Od0m0p1t0 ------------------------------
EXTENDS Naturals
CONSTANT Shift
VARIABLES tally, ledger

TypeOK = tally \in 0..Shift /\ ledger \in 0..Shift

Init == tally = 0 /\ ledger = 0

Commit == tally < Shift /\ tally' = 1 + tally /\ ledger' = ledger + 1
NextShift == tally = Shift /\ tally' = 0 /\ ledger' = 0

Next == Commit \/ NextShift

NoLostUpdate == tally = ledger

vars == <<tally, ledger>>
Spec == Init /\ [][Next]_vars
================================================================================