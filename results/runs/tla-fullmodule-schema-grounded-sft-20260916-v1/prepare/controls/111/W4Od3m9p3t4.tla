---------------------------- MODULE W4Od3m9p3t4 ----------------------------
EXTENDS Naturals

CONSTANTS Instr, MaxSlots, MaxEpoch

Slots == 1..MaxSlots

VARIABLES assigned, epoch, capacity, batchOpen

vars == <<assigned, epoch, capacity, batchOpen>>

SlotPairs(sl) == {pr \in assigned : pr[1] = sl}

TypeOK ==
    /\ assigned \subseteq (Slots \X Instr)
    /\ epoch \in 0..MaxEpoch
    /\ capacity \in 1..MaxSlots
    /\ batchOpen \in BOOLEAN

Init ==
    /\ assigned = {}
    /\ epoch = 0
    /\ capacity = MaxSlots
    /\ batchOpen = FALSE

OpenBatch ==
    /\ epoch < MaxEpoch
    /\ epoch' = epoch + 1
    /\ batchOpen' = TRUE
    /\ UNCHANGED <<assigned, capacity>>

Assign(sl, i) ==
    /\ batchOpen
    /\ sl <= capacity
    /\ SlotPairs(sl) = {}
    /\ assigned' = assigned \cup {<<sl, i>>}
    /\ UNCHANGED <<epoch, capacity, batchOpen>>

ChangeCapacity(k) ==
    /\ capacity' = k
    /\ UNCHANGED <<assigned, epoch, batchOpen>>

Release(sl) ==
    /\ SlotPairs(sl) # {}
    /\ assigned' = assigned \ SlotPairs(sl)
    /\ UNCHANGED <<epoch, capacity, batchOpen>>

Next ==
    \/ OpenBatch
    \/ \E sl \in Slots, i \in Instr : Assign(sl, i)
    \/ \E k \in 1..MaxSlots : ChangeCapacity(k)
    \/ \E sl \in Slots : Release(sl)

Spec == Init /\ [][Next]_vars

NoDoubleAssign ==
    \A sl \in Slots : \A i1, i2 \in Instr :
        (<<sl, i1>> \in assigned /\ <<sl, i2>> \in assigned) => (i1 = i2)

=============================================================================