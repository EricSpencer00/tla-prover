---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

CREATURES == 1..N

VARIABLES cstate, mall, totalMet

vars == <<cstate, mall, totalMet>>

Colors == {"blue", "red", "yellow", Faded}

\* The complement rule: the two participants adopt the unique third color,
\* or keep their shared color if they were already alike.
Complement(x, y) ==
    IF x = y THEN x
    ELSE CHOOSE c \in {"blue", "red", "yellow"} : c # x /\ c # y

TypeOK ==
    /\ cstate \in [CREATURES -> [color : Colors, met : 0..M]]
    /\ mall \in CREATURES \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ cstate = [c \in CREATURES |-> [color |-> CHOOSE c0 \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = 0

\* A creature enters the meeting place only while it is open and unoccupied.
Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet < M
    /\ cstate[c].color # Faded
    /\ mall' = c
    /\ UNCHANGED <<cstate, totalMet>>

\* When the meeting place is closed, a creature that tries to enter fades out.
FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = M
    /\ cstate[c].color # Faded
    /\ cstate' = [cstate EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, totalMet>>

\* Both participants adopt the complement color and count the meeting.
MeetAndMutate(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ cstate[c].color # Faded
    /\ totalMet < M
    /\ LET newc == Complement(cstate[c].color, cstate[mall].color) IN
         cstate' = [cstate EXCEPT ![c] = [color |-> newc, met |-> @.met + 1],
                                   ![mall] = [color |-> newc, met |-> @.met + 1]]
    /\ totalMet' = totalMet + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in CREATURES : Enter(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* At the point the meeting place closes, all meeting counts must sum to
\* exactly twice the number of completed meetings (each meeting is pairwise).
SumMet ==
    (LET f[S \in SUBSET CREATURES] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN cstate[x].met + f[S \ {x}]
     IN f[CREATURES]) = 2 * totalMet

\* The meeting place eventually closes once the meeting budget is spent.
Closed == totalMet = M

====