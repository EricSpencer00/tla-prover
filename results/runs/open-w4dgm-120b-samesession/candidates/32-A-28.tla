---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

\* A concurrency game between chameneos. Two creatures meet at a shared meeting
\* place and both adopt a new color given by the complement rule. A global
\* meeting counter caps how many meetings may occur; once it is reached, creatures
\* fade out instead of entering the place. Because each meeting involves exactly
\* two participants, once the place is closed the sum of individual meeting
\* counts equals twice the global total -- the conservation invariant below.
CONSTANTS N, M, Faded, MeetingPlaceEmpty

Assignments == [col: {"blue", "red", "yellow", Faded}, met: 0..M]

VARIABLES state, occupant, totalMet

vars == <<state, occupant, totalMet>>

TypeOK ==
    /\ state \in [1..N -> Assignments]
    /\ occupant \in (1..N) \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

SumOf(f, S) == LET g[T \in SUBSET S] ==
                    IF T = {} THEN 0
                    ELSE LET x == CHOOSE y \in T : TRUE
                         IN f[x] + g[T \ {x}]
               IN g[S]

Init ==
    /\ state = [c \in 1..N |-> [col |-> CHOOSE col \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
    /\ occupant = MeetingPlaceEmpty
    /\ totalMet = 0

Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE LET colors == {"blue", "red", "yellow"}
         IN CHOOSE col \in colors : col # c1 /\ col # c2

\* A creature enters the meeting place when it is empty and meetings remain.
EnterPlace(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ state[c].col # Faded
    /\ totalMet < M
    /\ occupant' = c
    /\ UNCHANGED <<state, totalMet>>

\* Once the meeting limit is reached, a creature that tries to enter fades.
FadeOut(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ state[c].col # Faded
    /\ state' = [state EXCEPT ![c].col = Faded]
    /\ UNCHANGED <<occupant, totalMet>>

\* Two different creatures meet; both adopt the complement color and count the
\* meeting. The global counter and the place both advance together.
Meet(c) ==
    /\ occupant # MeetingPlaceEmpty
    /\ occupant # c
    /\ totalMet < M
    /\ LET newcol == Complement(state[c].col, state[occupant].col)
       IN state' = [state EXCEPT ![c].col = newcol, ![c].met = @ + 1,
                                 ![occupant].col = newcol, ![occupant].met = @ + 1]
    /\ totalMet' = totalMet + 1
    /\ occupant' = MeetingPlaceEmpty

Next == \E c \in 1..N : EnterPlace(c) \/ FadeOut(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* When meetings are exhausted, the per-creature meeting counts sum to exactly
\* twice the total number of meetings -- every meeting counted both participants.
SumMet ==
    /\ (totalMet = M) => (SumOf([c \in 1..N |-> state[c].met], 1..N) = 2 * totalMet)

\* Not a bound but a bookkeeping fact: no creature can have attended more meetings
\* than the whole session ever allowed.
BoundedParticipation ==
    \A c \in 1..N : state[c].met <= M

====