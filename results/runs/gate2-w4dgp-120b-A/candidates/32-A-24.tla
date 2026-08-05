---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* N is the number of chameneos. M is the maximum number of meetings the
\* meeting place will support. Faded is the designated color of a creature
\* that has left the place. MeetingPlaceEmpty marks the place when nobody
\* is waiting.
Creatures == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumOver(f, S \ {x})

\* Complement: if two colors match the pair keeps them; otherwise both
\* adopt the third color in the set.
Complement(a, b) ==
    IF a = b THEN a
    ELSE LET colors == {"blue", "red", "yellow"}
         IN colors \ {a, b}

VARIABLES status, meetingPlace, totalMet
vars == <<status, meetingPlace, totalMet>>

TypeOK ==
    /\ status \in [Creatures -> [color : Colors, met : 0..(2 * M)]]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ status = [c \in Creatures |->
                    [color |-> CHOOSE col \in {"blue", "red", "yellow"} : TRUE,
                     met |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = 0

Enter(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet < M
    /\ status[c].color # Faded
    /\ meetingPlace' = c
    /\ UNCHANGED <<status, totalMet>>

FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = M
    /\ status[c].color # Faded
    /\ status' = [status EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<meetingPlace, totalMet>>

Meet(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ status[c].color # Faded
    /\ LET d == meetingPlace
           newc == Complement(status[c].color, status[d].color)
       IN /\ status' = [status EXCEPT ![c] = [color |-> newc, met |-> @.met + 1],
                        ![d] = [color |-> newc, met |-> @.met + 1]]
    /\ totalMet' = totalMet + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next == \E c \in Creatures : Enter(c) \/ FadeOut(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* Safety: every meeting counts for both participants, so the per-creature
\* totals add up to exactly twice the global meeting count once the
\* meeting place has closed.
SumMet ==
    (totalMet = M) => (SumOver([c \in Creatures |-> status[c].met], Creatures) = 2 * M)
====