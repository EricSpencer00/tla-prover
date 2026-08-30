---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature identifiers: 1..N; colors: three base colors plus the special
\* "faded" terminal color a creature takes once it is refused entry.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
BaseColors == {"blue", "red", "yellow"}

VARIABLES state, waiting, totalMeetings
vars == <<state, waiting, totalMeetings>>

\* Sum of the per-creature meeting counters; it equals twice the number of
\* meetings only when every meeting touched two participants exactly once.
RECURSIVE SumOf(_, _)
SumOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

TypeOK ==
    /\ state \in [Creatures -> [color: Colors, met: 0..M]]
    /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ state \in [Creatures -> [color: BaseColors, met: 0]]
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* The complement rule: same colors stay the same; different colors become the
\* third one not already held by either creature.
Complement(a, b) ==
    IF a = b THEN a
    ELSE LET x == CHOOSE c \in BaseColors : c # a /\ c # b IN x

Enter(c) ==
    /\ state[c].color # Faded
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ waiting' = c
    /\ UNCHANGED <<state, totalMeetings>>

Fade(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ state[c].color # Faded
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<waiting, totalMeetings>>

Meet(c) ==
    /\ waiting # MeetingPlaceEmpty
    /\ waiting # c
    /\ state[c].color # Faded
    /\ state[waiting].color # Faded
    /\ totalMeetings < M
    /\ LET newcol == Complement(state[c].color, state[waiting].color) IN
        /\ state' = [state EXCEPT
                        ![c].color = newcol,
                        ![c].met = @ + 1,
                        ![waiting].color = newcol,
                        ![waiting].met = @ + 1]
    /\ totalMeetings' = totalMeetings + 1
    /\ waiting' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : Fade(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* SAFETY: at the meeting ceiling the per-creature counts still add up to
\* exactly twice the number of meetings -- nothing is double-counted or lost.
SumMet == (totalMeetings = M) => SumOf(state[*].met, Creatures) = 2 * M
====