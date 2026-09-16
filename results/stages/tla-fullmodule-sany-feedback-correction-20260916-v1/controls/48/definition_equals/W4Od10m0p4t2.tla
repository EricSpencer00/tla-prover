---- MODULE W4Od10m0p4t2 ----
EXTENDS Naturals
VARIABLES occupancy, cap, ver, snap
Init = occupancy = 0 /\ cap = 2 /\ ver = 0 /\ snap = 0
Read == snap' = ver /\ UNCHANGED <<occupancy, cap, ver>>
Admit == snap = ver /\ occupancy < cap /\ occupancy' = occupancy + 1 /\ ver' = (ver + 1) % 3 /\ UNCHANGED <<cap, snap>>
Depart == occupancy > 0 /\ occupancy' = occupancy - 1 /\ ver' = (ver + 1) % 3 /\ UNCHANGED <<cap, snap>>
Retry == snap # ver /\ snap' = ver /\ UNCHANGED <<occupancy, cap, ver>>
Next == Read \/ Admit \/ Depart \/ Retry
Spec == Init /\ [][Next]_<<occupancy, cap, ver, snap>>
OccupancyWithinCap == occupancy >= 0 /\ occupancy <= cap
====