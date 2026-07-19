-------------------------- MODULE W4Od19m6p5t3 --------------------------
EXTENDS Naturals

CONSTANTS Staff, Copies, NoOne, MaxClock, LeaseDur

VARIABLES
    clock,          \* shared clock
    holder,         \* current station lease holder, or NoOne
    expiry,         \* clock time the lease lapses
    state,          \* state[c] : "available" | "archived"
    archiveCount    \* archiveCount[c] : times copy c has been archived

vars == << clock, holder, expiry, state, archiveCount >>

TypeOK ==
    /\ clock \in 0..MaxClock
    /\ holder \in (Staff \cup {NoOne})
    /\ expiry \in 0..(MaxClock + LeaseDur)
    /\ state \in [Copies -> {"available", "archived"}]
    /\ archiveCount \in [Copies -> 0..2]

Init ==
    /\ clock = 0
    /\ holder = NoOne
    /\ expiry = 0
    /\ state = [c \in Copies |-> "available"]
    /\ archiveCount = [c \in Copies |-> 0]

LeaseFree == (holder = NoOne) \/ (expiry <= clock)

Acquire(p) ==
    /\ LeaseFree
    /\ holder' = p
    /\ expiry' = clock + LeaseDur
    /\ UNCHANGED << clock, state, archiveCount >>

\* Only a valid-lease holder may irreversibly archive an available copy.
Archive(p, c) ==
    /\ holder = p
    /\ expiry > clock
    /\ state[c] = "available"
    /\ state' = [state EXCEPT ![c] = "archived"]
    /\ archiveCount' = [archiveCount EXCEPT ![c] = @ + 1]
    /\ UNCHANGED << clock, holder, expiry >>

Release(p) ==
    /\ holder = p
    /\ holder' = NoOne
    /\ UNCHANGED << clock, expiry, state, archiveCount >>

Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED << holder, expiry, state, archiveCount >>

Next ==
    \/ \E p \in Staff : Acquire(p)
    \/ \E p \in Staff, c \in Copies : Archive(p, c)
    \/ \E p \in Staff : Release(p)
    \/ Tick

Spec == Init /\ [][Next]_vars

\* The irreversible archiving of each copy happens at most once.
ArchiveAtMostOnce == \A c \in Copies : archiveCount[c] <= 1

=============================================================================
