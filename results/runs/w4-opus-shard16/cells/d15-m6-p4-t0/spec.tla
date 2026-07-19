-------------------------- MODULE W4Od15m6p4t0 --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Makers, OrderSlots, NoOne, MaxClock, LeaseDur, Cap

VARIABLES
    clock,      \* shared clock
    holder,     \* current lease holder, or NoOne
    expiry,     \* clock time the lease lapses
    orders,     \* set of occupied order slots in the book
    crashed     \* set of silently-crashed makers

vars == << clock, holder, expiry, orders, crashed >>

TypeOK ==
    /\ clock \in 0..MaxClock
    /\ holder \in (Makers \cup {NoOne})
    /\ expiry \in 0..(MaxClock + LeaseDur)
    /\ orders \subseteq OrderSlots
    /\ crashed \subseteq Makers

Init ==
    /\ clock = 0
    /\ holder = NoOne
    /\ expiry = 0
    /\ orders = {}
    /\ crashed = {}

LeaseFree == (holder = NoOne) \/ (expiry <= clock)
Valid(t) == (holder = t) /\ (expiry > clock)

Acquire(t) ==
    /\ t \notin crashed
    /\ LeaseFree
    /\ holder' = t
    /\ expiry' = clock + LeaseDur
    /\ UNCHANGED << clock, orders, crashed >>

\* Submit a new order only while the book has room.
Submit(t, o) ==
    /\ t \notin crashed
    /\ Valid(t)
    /\ o \notin orders
    /\ Cardinality(orders) < Cap
    /\ orders' = orders \cup {o}
    /\ UNCHANGED << clock, holder, expiry, crashed >>

Cancel(t, o) ==
    /\ t \notin crashed
    /\ Valid(t)
    /\ o \in orders
    /\ orders' = orders \ {o}
    /\ UNCHANGED << clock, holder, expiry, crashed >>

Release(t) ==
    /\ t \notin crashed
    /\ holder = t
    /\ holder' = NoOne
    /\ UNCHANGED << clock, expiry, orders, crashed >>

Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED << holder, expiry, orders, crashed >>

Crash(t) ==
    /\ t \notin crashed
    /\ crashed' = crashed \cup {t}
    /\ UNCHANGED << clock, holder, expiry, orders >>

Recover(t) ==
    /\ t \in crashed
    /\ crashed' = crashed \ {t}
    /\ UNCHANGED << clock, holder, expiry, orders >>

Next ==
    \/ \E t \in Makers : Acquire(t)
    \/ \E t \in Makers, o \in OrderSlots : Submit(t, o)
    \/ \E t \in Makers, o \in OrderSlots : Cancel(t, o)
    \/ \E t \in Makers : Release(t)
    \/ Tick
    \/ \E t \in Makers : Crash(t)
    \/ \E t \in Makers : Recover(t)

Spec == Init /\ [][Next]_vars

\* Bounded capacity: the book never holds more than Cap resting orders.
WithinCapacity == Cardinality(orders) <= Cap

=============================================================================
