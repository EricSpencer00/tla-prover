-------------------------- MODULE W4Od7m9p1t4 --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Cranes, MaxEpoch, MaxVer, MaxCap

VARIABLES
    curEpoch,   \* hub's current epoch
    known,      \* known[c] : epoch crane c last learned
    version,    \* live version of the shared stow-plan record
    lastBase,   \* base version the latest commit built on
    reserved,   \* set of cranes currently holding a working reservation
    snap,       \* snap[c] : version a reserved crane snapshotted
    capacity    \* max concurrent reservations (changes at runtime)

vars == << curEpoch, known, version, lastBase, reserved, snap, capacity >>

TypeOK ==
    /\ curEpoch \in 0..MaxEpoch
    /\ known \in [Cranes -> 0..MaxEpoch]
    /\ version \in 0..MaxVer
    /\ lastBase \in 0..MaxVer
    /\ reserved \subseteq Cranes
    /\ snap \in [Cranes -> 0..MaxVer]
    /\ capacity \in 0..MaxCap

Init ==
    /\ curEpoch = 0
    /\ known = [c \in Cranes |-> 0]
    /\ version = 0
    /\ lastBase = 0
    /\ reserved = {}
    /\ snap = [c \in Cranes |-> 0]
    /\ capacity = 1

Reconfigure ==
    /\ curEpoch < MaxEpoch
    /\ curEpoch' = curEpoch + 1
    /\ UNCHANGED << known, version, lastBase, reserved, snap, capacity >>

Adopt(c) ==
    /\ known[c] < curEpoch
    /\ known' = [known EXCEPT ![c] = curEpoch]
    /\ UNCHANGED << curEpoch, version, lastBase, reserved, snap, capacity >>

\* Take a reservation if current and capacity allows; snapshot the version.
Reserve(c) ==
    /\ known[c] = curEpoch
    /\ c \notin reserved
    /\ Cardinality(reserved) < capacity
    /\ reserved' = reserved \cup {c}
    /\ snap' = [snap EXCEPT ![c] = version]
    /\ UNCHANGED << curEpoch, known, version, lastBase, capacity >>

\* Commit only with a reservation and a still-current snapshot.
Commit(c) ==
    /\ c \in reserved
    /\ snap[c] = version
    /\ version < MaxVer
    /\ version' = version + 1
    /\ lastBase' = snap[c]
    /\ reserved' = reserved \ {c}
    /\ UNCHANGED << curEpoch, known, snap, capacity >>

ReleaseReservation(c) ==
    /\ c \in reserved
    /\ reserved' = reserved \ {c}
    /\ UNCHANGED << curEpoch, known, version, lastBase, snap, capacity >>

Grow ==
    /\ capacity < MaxCap
    /\ capacity' = capacity + 1
    /\ UNCHANGED << curEpoch, known, version, lastBase, reserved, snap >>

Shrink ==
    /\ capacity > 0
    /\ Cardinality(reserved) <= capacity - 1
    /\ capacity' = capacity - 1
    /\ UNCHANGED << curEpoch, known, version, lastBase, reserved, snap >>

Next ==
    \/ Reconfigure
    \/ \E c \in Cranes : Adopt(c)
    \/ \E c \in Cranes : Reserve(c)
    \/ \E c \in Cranes : Commit(c)
    \/ \E c \in Cranes : ReleaseReservation(c)
    \/ Grow
    \/ Shrink

Spec == Init /\ [][Next]_vars

\* No lost updates: each commit built on its immediate predecessor version.
NoLostUpdate == (version = 0) \/ (lastBase = version - 1)

=============================================================================
