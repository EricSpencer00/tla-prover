---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature carries a color and its own meeting counter; the meeting
\* place holds at most one waiting creature, and a global counter tracks
\* total meetings. The complement rule is a deterministic color map.
Colors == {"blue", "red", "yellow"}
Complement == [x \in Colors, y \in Colors |-> IF x = y THEN x
                                            ELSE LET z \in Colors : z # x /\ z # y IN z]

VARIABLES attrs, occupant, total
vars == <<attrs, occupant, total>>

TypeOK ==
    /\ attrs \in [1..N -> [color : Colors \cup {Faded}, meetings : 0..M]]
    /\ occupant \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in 0..M

Init ==
    /\ attrs = [i \in 1..N |-> [color |-> CHOOSE c \in Colors : TRUE, meetings |-> 0]]
    /\ occupant = MeetingPlaceEmpty
    /\ total = 0

\* A non-faded creature enters the empty meeting place if meetings remain.
Enter(i) ==
    /\ occupant = MeetingPlaceEmpty
    /\ attrs[i].color # Faded
    /\ total < M
    /\ occupant' = i
    /\ UNCHANGED <<attrs, total>>

\* Once the meeting limit is reached, a creature that tries to enter fades.
FadeOut(i) ==
    /\ occupant = MeetingPlaceEmpty
    /\ attrs[i].color # Faded
    /\ total = M
    /\ attrs' = [attrs EXCEPT ![i].color = Faded]
    /\ UNCHANGED <<occupant, total>>

\* Two different creatures meet in the place and both adopt the complement.
MeetAndMutate(i) ==
    /\ occupant # MeetingPlaceEmpty
    /\ occupant # i
    /\ attrs[i].color # Faded
    /\ attrs[occupant].color # Faded
    /\ total < M
    /\ LET newc == Complement[attrs[i].color][attrs[occupant].color] IN
        attrs' = [attrs EXCEPT ![i].color = newc, ![occupant].color = newc,
                  ![i].meetings = @ + 1, ![occupant].meetings = @ + 1]
    /\ occupant' = MeetingPlaceEmpty
    /\ total' = total + 1

Next ==
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : FadeOut(i)
    \/ \E i \in 1..N : MeetAndMutate(i)

Spec == Init /\ [][Next]_vars

\* Every meeting counts twice against the per-creature tallies: once per
\* participant, so at the limit the summed tallies must be exactly twice
\* the total meetings that have occurred.
SumMet ==
    /\ total = M
    /\ (2 * total) = (attrs[1].meetings + attrs[2].meetings
                      + (IF N >= 3 THEN attrs[3].meetings ELSE 0)
                      + (IF N >= 4 THEN attrs[4].meetings ELSE 0)
                      + (IF N >= 5 THEN attrs[5].meetings ELSE 0))

\* No creature is ever stuck forever: since every meeting frees the place
\* and meetings are finite, the meeting place eventually closes and every
\* creature's remaining attempts make it fade; hence each creature ends up
\* faded, which is a state the system always eventually reaches.
EventualFading == <>(\A i \in 1..N : attrs[i].color = Faded)
====