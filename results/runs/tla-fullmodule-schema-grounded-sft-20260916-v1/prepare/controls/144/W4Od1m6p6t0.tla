---- MODULE W4Od1m6p6t0 ----
EXTENDS Naturals

CONSTANTS Controllers, Runways, MaxGeneration, NoController, NoRunway

ASSUME NoController \notin Controllers
ASSUME NoRunway \notin Runways

VARIABLES generation, holder, cutIn, up, clearing, clearedIn

vars == <<generation, holder, cutIn, up, clearing, clearedIn>>

TypeOK ==
    /\ generation \in 0 .. MaxGeneration
    /\ holder \in [Runways -> Controllers \cup {NoController}]
    /\ cutIn \in [Runways -> 0 .. MaxGeneration]
    /\ up \in SUBSET Controllers
    /\ clearing \in [Controllers -> Runways \cup {NoRunway}]
    /\ clearedIn \in [Controllers -> 0 .. MaxGeneration]

Init ==
    /\ generation = 0
    /\ holder = [r \in Runways |-> NoController]
    /\ cutIn = [r \in Runways |-> 0]
    /\ up = Controllers
    /\ clearing = [c \in Controllers |-> NoRunway]
    /\ clearedIn = [c \in Controllers |-> 0]

Working == {c \in Controllers : clearing[c] \in Runways}
Authorised ==
    {c \in Controllers :
        /\ clearing[c] \in Runways
        /\ holder[clearing[c]] = c
        /\ cutIn[clearing[c]] = generation}

Grant(c, r) ==
    /\ c \in up
    /\ holder[r] = NoController
    /\ holder' = [holder EXCEPT ![r] = c]
    /\ cutIn' = [cutIn EXCEPT ![r] = generation]
    /\ UNCHANGED <<generation, up, clearing, clearedIn>>

\* Winding the generation on is what makes leases stale, so it waits for
\* an empty pattern.
Advance ==
    /\ generation < MaxGeneration
    /\ Working = {}
    /\ generation' = generation + 1
    /\ UNCHANGED <<holder, cutIn, up, clearing, clearedIn>>

\* Recovery is by generation, not by detection: nobody has to notice.
Reap(r) ==
    /\ holder[r] # NoController
    /\ cutIn[r] < generation
    /\ holder' = [holder EXCEPT ![r] = NoController]
    /\ UNCHANGED <<generation, cutIn, up, clearing, clearedIn>>

Clear(c, r) ==
    /\ c \in up
    /\ clearing[c] = NoRunway
    /\ holder[r] = c
    /\ cutIn[r] = generation
    /\ clearedIn[c] # generation
    /\ clearing' = [clearing EXCEPT ![c] = r]
    /\ clearedIn' = [clearedIn EXCEPT ![c] = generation]
    /\ UNCHANGED <<generation, holder, cutIn, up>>

Complete(c) ==
    /\ clearing[c] \in Runways
    /\ clearing' = [clearing EXCEPT ![c] = NoRunway]
    /\ UNCHANGED <<generation, holder, cutIn, up, clearedIn>>

\* No alarm, no handover, nothing to distinguish this from being quiet.
Fail(c) ==
    /\ c \in up
    /\ up' = up \ {c}
    /\ UNCHANGED <<generation, holder, cutIn, clearing, clearedIn>>

Return(c) ==
    /\ c \notin up
    /\ up' = up \cup {c}
    /\ UNCHANGED <<generation, holder, cutIn, clearing, clearedIn>>

Next ==
    \/ \E c \in Controllers, r \in Runways : Grant(c, r)
    \/ Advance
    \/ \E r \in Runways : Reap(r)
    \/ \E c \in Controllers, r \in Runways : Clear(c, r)
    \/ \E c \in Controllers : Complete(c)
    \/ \E c \in Controllers : Fail(c)
    \/ \E c \in Controllers : Return(c)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E c \in Controllers : Complete(c))

\* Anyone working a clearance holds that runway's lease, cut in this generation.
ClearancesRestOnLiveAuthority == Working \subseteq Authorised

PatternAlwaysEmpties == (Working # {}) ~> (Working = {})

====