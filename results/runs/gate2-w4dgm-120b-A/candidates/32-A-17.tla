---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature ids are 1..N; colors are the three base colors plus "faded".
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

\* The complement rule: different colors resolve to the third, equal colors stay.
Complement(a, b) ==
    IF a = b THEN a
    ELSE LET c \in Colors \ {a, b} IN c

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

VARIABLES cstate, mall, totalMeetings
vars == <<cstate, mall, totalMeetings>>

TypeOK ==
    /\ cstate \in [Creatures -> [col : Colors, done : 0..M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ cstate \in [Creatures -> [col : {"blue", "red", "yellow"}, done : 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* A non-faded creature enters the empty meeting place before the cap closes.
Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ cstate[c].col # Faded
    /\ mall' = c
    /\ UNCHANGED <<cstate, totalMeetings>>

\* With the place closed, a non-faded creature that still tries fades out.
Fade(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ cstate[c].col # Faded
    /\ cstate' = [cstate EXCEPT ![c] = [col |-> Faded, done |-> @.done]]
    /\ UNCHANGED <<mall, totalMeetings>>

\* The pair adopt the complement color and both log the meeting.
Meet(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ totalMeetings < M
    /\ cstate[c].col # Faded
    /\ LET newcol == Complement(cstate[c].col, cstate[mall].col) IN
        /\ cstate' = [cstate EXCEPT ![c] = [col |-> newcol, done |-> @.done + 1],
                              ![mall] = [col |-> newcol, done |-> @.done + 1]]
    /\ totalMeetings' = totalMeetings + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \E c \in Creatures : Enter(c) \/ Fade(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* Every meeting adds exactly two to the summed participation count.
ConcurrencyAccounted ==
    totalMeetings = M => SumOver([g \in Creatures |-> cstate[g].done], Creatures) = 2 * M

TypeOKInv == TypeOK
====