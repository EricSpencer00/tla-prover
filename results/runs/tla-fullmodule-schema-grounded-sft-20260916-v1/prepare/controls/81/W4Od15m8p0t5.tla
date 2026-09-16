-------------------------- MODULE W4Od15m8p0t5 --------------------------
\* Stock-exchange opening auction. Each order book is a critical resource whose
\* matching engine must run under mutual exclusion. Access is protected by a
\* two-level (hierarchical) lock: a trader must first hold the coarse session
\* lock before it may take the fine per-book lock, and only the holder of a
\* book's fine lock may run that book's opening match. A privileged exchange
\* admin may forcibly seize any fine lock to intervene, without disturbing the
\* mutual-exclusion discipline.
EXTENDS Naturals, FiniteSets

CONSTANTS Traders, Books, Admin, None

\* coarse: holder of the coarse session lock or None; fine[b]: holder of book
\* b's fine lock or None; matched[b]: whether b's opening auction has matched;
\* overridden: the set of books the admin has forcibly seized.
VARIABLES coarse, fine, matched, overridden

vars == <<coarse, fine, matched, overridden>>

Actors == Traders \cup {Admin}

TypeOK ==
    /\ coarse \in Traders \cup {None}
    /\ fine \in [Books -> Actors \cup {None}]
    /\ matched \in [Books -> BOOLEAN]
    /\ overridden \subseteq Books

Init ==
    /\ coarse = None
    /\ fine = [b \in Books |-> None]
    /\ matched = [b \in Books |-> FALSE]
    /\ overridden = {}

\* Take the coarse session lock when it is free.
AcquireCoarse(t) ==
    /\ coarse = None
    /\ coarse' = t
    /\ UNCHANGED <<fine, matched, overridden>>

\* Take a book's fine lock -- only permitted to the coarse-lock holder.
AcquireFine(t, b) ==
    /\ coarse = t
    /\ fine[b] = None
    /\ fine' = [fine EXCEPT ![b] = t]
    /\ UNCHANGED <<coarse, matched, overridden>>

\* Run a book's opening match under its fine lock.
MatchBook(t, b) ==
    /\ fine[b] = t
    /\ matched[b] = FALSE
    /\ matched' = [matched EXCEPT ![b] = TRUE]
    /\ UNCHANGED <<coarse, fine, overridden>>

\* Release a fine lock held by the actor.
ReleaseFine(t, b) ==
    /\ fine[b] = t
    /\ fine' = [fine EXCEPT ![b] = None]
    /\ UNCHANGED <<coarse, matched, overridden>>

\* Release the coarse lock, permitted only once no fine lock is still held.
ReleaseCoarse(t) ==
    /\ coarse = t
    /\ \A b \in Books : fine[b] # t
    /\ coarse' = None
    /\ UNCHANGED <<fine, matched, overridden>>

\* Privileged admin override: forcibly seize a book's fine lock, once per book.
AdminOverride(b) ==
    /\ b \notin overridden
    /\ fine' = [fine EXCEPT ![b] = Admin]
    /\ overridden' = overridden \cup {b}
    /\ UNCHANGED <<coarse, matched>>

Next ==
    \/ \E t \in Traders : AcquireCoarse(t)
    \/ \E t \in Traders, b \in Books : AcquireFine(t, b)
    \/ \E t \in Actors, b \in Books : MatchBook(t, b)
    \/ \E t \in Actors, b \in Books : ReleaseFine(t, b)
    \/ \E t \in Traders : ReleaseCoarse(t)
    \/ \E b \in Books : AdminOverride(b)

Spec == Init /\ [][Next]_vars

StateBound == Cardinality(overridden) <= Cardinality(Books)

\* Every held fine lock belongs either to the single current coarse-lock holder
\* or to the privileged admin. Since at most one trader holds the coarse lock,
\* no two competing traders can hold fine locks at once: mutual exclusion of the
\* critical order-book resource is enforced by the lock hierarchy.
LockHierarchy ==
    \A b \in Books :
        fine[b] # None => (fine[b] = coarse \/ fine[b] = Admin)
=============================================================================