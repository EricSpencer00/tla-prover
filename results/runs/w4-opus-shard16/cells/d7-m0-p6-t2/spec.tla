-------------------------- MODULE W4Od7m0p6t2 --------------------------
EXTENDS Naturals

CONSTANTS Workers, Cells, NoCell, MaxVer

VARIABLES
    version,    \* version[cell] : live version number of each pool cell
    lastBase,   \* lastBase[cell] : snapshot the last commit to cell used
    attempt,    \* attempt[w] : cell a worker is trying to change, or NoCell
    snap,       \* snap[w] : version the worker read when it started
    registered  \* set of currently registered (authorized) workers

vars == << version, lastBase, attempt, snap, registered >>

TypeOK ==
    /\ version \in [Cells -> 0..MaxVer]
    /\ lastBase \in [Cells -> 0..MaxVer]
    /\ attempt \in [Workers -> (Cells \cup {NoCell})]
    /\ snap \in [Workers -> 0..MaxVer]
    /\ registered \subseteq Workers

Init ==
    /\ version = [c \in Cells |-> 0]
    /\ lastBase = [c \in Cells |-> 0]
    /\ attempt = [w \in Workers |-> NoCell]
    /\ snap = [w \in Workers |-> 0]
    /\ registered = Workers

\* A registered worker reads a cell and snapshots its version.
Read(w, c) ==
    /\ w \in registered
    /\ attempt[w] = NoCell
    /\ attempt' = [attempt EXCEPT ![w] = c]
    /\ snap' = [snap EXCEPT ![w] = version[c]]
    /\ UNCHANGED << version, lastBase, registered >>

\* Commit succeeds only if the worker is registered and not stale.
Commit(w) ==
    /\ w \in registered
    /\ attempt[w] # NoCell
    /\ snap[w] = version[attempt[w]]
    /\ version[attempt[w]] < MaxVer
    /\ version' = [version EXCEPT ![attempt[w]] = @ + 1]
    /\ lastBase' = [lastBase EXCEPT ![attempt[w]] = snap[w]]
    /\ attempt' = [attempt EXCEPT ![w] = NoCell]
    /\ UNCHANGED << snap, registered >>

\* A stale worker re-reads the current version and tries again.
Retry(w) ==
    /\ attempt[w] # NoCell
    /\ snap[w] # version[attempt[w]]
    /\ snap' = [snap EXCEPT ![w] = version[attempt[w]]]
    /\ UNCHANGED << version, lastBase, attempt, registered >>

\* The supervisor revokes a worker, cancelling any in-flight attempt.
Revoke(w) ==
    /\ w \in registered
    /\ registered' = registered \ {w}
    /\ attempt' = [attempt EXCEPT ![w] = NoCell]
    /\ UNCHANGED << version, lastBase, snap >>

\* A revoked worker is re-registered.
Register(w) ==
    /\ w \notin registered
    /\ registered' = registered \cup {w}
    /\ UNCHANGED << version, lastBase, attempt, snap >>

Next ==
    \/ \E w \in Workers, c \in Cells : Read(w, c)
    \/ \E w \in Workers : Commit(w)
    \/ \E w \in Workers : Retry(w)
    \/ \E w \in Workers : Revoke(w)
    \/ \E w \in Workers : Register(w)

Spec == Init /\ [][Next]_vars

\* No stale write ever took effect: each cell's latest commit built on the
\* version directly beneath the current one.
NoStaleWrite ==
    \A c \in Cells : (version[c] = 0) \/ (lastBase[c] = version[c] - 1)

=============================================================================
