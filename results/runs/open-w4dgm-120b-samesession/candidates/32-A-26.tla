---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature's state: a color (three real colors plus the faded marker) and a
\* personal meeting count. The meeting place holds at most one waiting creature.
\* The global counter caps the whole system's meetings.
Creatures == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}

VARIABLES status, meetingPlace, totalMet

vars == <<status, meetingPlace, totalMet>>

TypeOK ==
    /\ status \in [Creatures -> [color: Colors, met: 0..M]]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

SumMet ==
    LET g[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN status[x].met + g[S \ {x}]
    IN g[Creatures]

Init ==
    /\ \E c \in [Creatures -> {"blue","red","yellow"}]:
         status = [k \in Creatures |-> [color |-> c[k], met |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = 0

Enter(k) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ status[k].color # Faded
    /\ totalMet < M
    /\ meetingPlace' = k
    /\ UNCHANGED <<status, totalMet>>

Fade(k) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ status[k].color # Faded
    /\ totalMet = M
    /\ status' = [status EXCEPT ![k].color = Faded]
    /\ UNCHANGED <<meetingPlace, totalMet>>

\* The complement rule: same color -> unchanged; different colors -> both adopt
\* the third (missing) color from the triangle of three real colors.
Complement(x, y) ==
    IF status[x].color = status[y].color
    THEN status[x].color
    ELSE LET colors == {"blue", "red", "yellow"}
             in colors \ {status[x].color, status[y].color}
                 \in {status[x].color, status[y].color}

Meet(k) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ k # meetingPlace
    /\ status[k].color # Faded
    /\ status[meetingPlace].color # Faded
    /\ totalMet < M
    /\ status' = [status EXCEPT
           ![k].color = Complement(k, meetingPlace),
           ![k].met = @ + 1,
           ![meetingPlace].color = Complement(k, meetingPlace),
           ![meetingPlace].met = @ + 1]
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ totalMet' = totalMet + 1

Next == \E k \in Creatures: Enter(k) \/ Fade(k) \/ Meet(k)

Spec == Init /\ [][Next]_vars

\* Every meeting touches two participants, so when the meeting budget is spent
\* the personal counts sum to exactly twice the number of meetings.
MeetingBudgetFullySpent == (totalMet = M) => (SumMet = 2 * totalMet)

====