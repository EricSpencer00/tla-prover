-------------------------- MODULE W4Od16m6p1t0 --------------------------
EXTENDS Naturals

CONSTANTS Pharmacists, NoOne, MaxClock, LeaseDur, MaxVer

VARIABLES
    clock,        \* shared monotonic clock
    holder,       \* current lease owner, or NoOne
    expiry,       \* clock time at which the current lease expires
    version,      \* version number of the shared record
    lastSnap,     \* snapshot the most recent committed write was based on
    snap,         \* per-pharmacist version snapshot taken at lease acquire
    crashed       \* set of pharmacists that have crashed silently

vars == << clock, holder, expiry, version, lastSnap, snap, crashed >>

TypeOK ==
    /\ clock \in 0..MaxClock
    /\ holder \in (Pharmacists \cup {NoOne})
    /\ expiry \in 0..(MaxClock + LeaseDur)
    /\ version \in 0..MaxVer
    /\ lastSnap \in 0..MaxVer
    /\ snap \in [Pharmacists -> 0..MaxVer]
    /\ crashed \subseteq Pharmacists

Init ==
    /\ clock = 0
    /\ holder = NoOne
    /\ expiry = 0
    /\ version = 0
    /\ lastSnap = 0
    /\ snap = [p \in Pharmacists |-> 0]
    /\ crashed = {}

LeaseFree == (holder = NoOne) \/ (expiry <= clock)

\* A pharmacist grabs the record's lease when it is free or has expired.
Acquire(p) ==
    /\ p \notin crashed
    /\ LeaseFree
    /\ holder' = p
    /\ expiry' = clock + LeaseDur
    /\ snap' = [snap EXCEPT ![p] = version]
    /\ UNCHANGED << clock, version, lastSnap, crashed >>

\* The owner commits an update only while its lease is valid and only if the
\* record has not moved since it took its snapshot.
Commit(p) ==
    /\ p \notin crashed
    /\ holder = p
    /\ clock < expiry
    /\ snap[p] = version
    /\ version < MaxVer
    /\ version' = version + 1
    /\ lastSnap' = snap[p]
    /\ holder' = NoOne
    /\ UNCHANGED << clock, expiry, snap, crashed >>

\* A non-crashed owner may release its lease explicitly.
Release(p) ==
    /\ p \notin crashed
    /\ holder = p
    /\ holder' = NoOne
    /\ UNCHANGED << clock, expiry, version, lastSnap, snap, crashed >>

\* The shared clock advances, which lets stale leases expire.
Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED << holder, expiry, version, lastSnap, snap, crashed >>

\* A pharmacist crashes silently: it stops acting but keeps its lease.
Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED << clock, holder, expiry, version, lastSnap, snap >>

\* A crashed pharmacist may later revive and resume work.
Recover(p) ==
    /\ p \in crashed
    /\ crashed' = crashed \ {p}
    /\ UNCHANGED << clock, holder, expiry, version, lastSnap, snap >>

Next ==
    \/ Tick
    \/ \E p \in Pharmacists : Acquire(p)
    \/ \E p \in Pharmacists : Commit(p)
    \/ \E p \in Pharmacists : Release(p)
    \/ \E p \in Pharmacists : Crash(p)
    \/ \E p \in Pharmacists : Recover(p)

Spec == Init /\ [][Next]_vars

\* No lost updates: the most recent commit was based on the version that
\* immediately preceded it, so no committed write ever skipped over and
\* discarded another pharmacist's update.
NoLostUpdate == (version = 0) \/ (lastSnap = version - 1)

=============================================================================
