-------------------------- MODULE W4Od4m7p0t3 --------------------------
EXTENDS Naturals

CONSTANTS Controllers, FREE, MaxTag

VARIABLES
    owner,      \* the compare-and-swap register's owner, or FREE
    tag,        \* rotating tag stored alongside the owner
    pc,         \* pc[c] : "idle" | "trying" | "spraying"
    snapTag     \* snapTag[c] : tag a controller snapshotted when it started

vars == << owner, tag, pc, snapTag >>

TypeOK ==
    /\ owner \in (Controllers \cup {FREE})
    /\ tag \in 0..MaxTag
    /\ pc \in [Controllers -> {"idle", "trying", "spraying"}]
    /\ snapTag \in [Controllers -> 0..MaxTag]

Init ==
    /\ owner = FREE
    /\ tag = 0
    /\ pc = [c \in Controllers |-> "idle"]
    /\ snapTag = [c \in Controllers |-> 0]

\* Signal interest and snapshot the register's current tag.
Try(c) ==
    /\ pc[c] = "idle"
    /\ pc' = [pc EXCEPT ![c] = "trying"]
    /\ snapTag' = [snapTag EXCEPT ![c] = tag]
    /\ UNCHANGED << owner, tag >>

\* Compare-and-swap succeeds only if still free and the tag is unchanged.
CAS(c) ==
    /\ pc[c] = "trying"
    /\ owner = FREE
    /\ tag = snapTag[c]
    /\ owner' = c
    /\ pc' = [pc EXCEPT ![c] = "spraying"]
    /\ UNCHANGED << tag, snapTag >>

\* A failed swap backs off to idle.
Backoff(c) ==
    /\ pc[c] = "trying"
    /\ (owner # FREE \/ tag # snapTag[c])
    /\ pc' = [pc EXCEPT ![c] = "idle"]
    /\ UNCHANGED << owner, tag, snapTag >>

\* The owner frees the register and advances the tag.
Exit(c) ==
    /\ pc[c] = "spraying"
    /\ owner = c
    /\ owner' = FREE
    /\ tag' = IF tag < MaxTag THEN tag + 1 ELSE 0
    /\ pc' = [pc EXCEPT ![c] = "idle"]
    /\ UNCHANGED snapTag

Next ==
    \/ \E c \in Controllers : Try(c)
    \/ \E c \in Controllers : CAS(c)
    \/ \E c \in Controllers : Backoff(c)
    \/ \E c \in Controllers : Exit(c)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: at most one controller sprays at once.
SprayerExclusion ==
    \A a, b \in Controllers :
        (pc[a] = "spraying" /\ pc[b] = "spraying") => (a = b)

=============================================================================
