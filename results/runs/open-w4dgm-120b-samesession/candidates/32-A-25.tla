---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0 /\ Faded \in {"faded"}
        /\ MeetingPlaceEmpty \in {"empty"}

\* Creature identifiers are 0..N-1; colors are the three primary ones plus
\* a distinguished faded color. Colors held in a set for fast complement.
Creatures == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}

VARIABLES status, meetingPlace, totalMeetings

vars == <<status, meetingPlace, totalMeetings>>

TypeOK ==
    /\ status \in [Creatures -> [col: Colors, cnt: 0..M]]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ status = [c \in Creatures |-> [col |-> CHOOSE k \in Colors : k # Faded,
                                         cnt |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* The complement rule: two equal colors stay; two different colors both
\* become the third, computed as the set difference from the full set.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE k \in Colors \ {c1, c2} : TRUE

EnterMall(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ status[c].col # Faded
    /\ totalMeetings < M
    /\ meetingPlace' = c
    /\ UNCHANGED <<status, totalMeetings>>

FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ status[c].col # Faded
    /\ totalMeetings >= M
    /\ status' = [status EXCEPT ![c].col = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* The two creatures are distinct by construction; both adopt the same
\* complement color and both get credit for the meeting.
Meet(c, w) ==
    /\ meetingPlace = w
    /\ w # c
    /\ status[c].col # Faded
    /\ status[w].col # Faded
    /\ totalMeetings < M
    /\ LET newcol == Complement(status[c].col, status[w].col) IN
         status' = [status EXCEPT ![c] = [col |-> newcol, cnt |-> @.cnt + 1],
                                 ![w] = [col |-> newcol, cnt |-> @.cnt + 1]]
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E c \in Creatures : EnterMall(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures, w \in Creatures : Meet(c, w)

Spec == Init /\ [][Next]_vars

SumCounts == LET add[S \in SUBSET Creatures] ==
                 IF S = {} THEN 0
                 ELSE LET x == CHOOSE y \in S : TRUE IN status[x].cnt + add[S \ {x}]
             IN add[Creatures]

\* Every meeting counts exactly twice toward the individual counters, so
\* when the meeting budget is spent the summed participation is exactly
\* twice the number of meetings that happened.
SumMet == totalMeetings = M => SumCounts = 2 * M

\* Bounded capacity: the meeting place never holds two waiting creatures
\* at once. The literal shape of the invariant is that the meeting place
\* holds a creature identifier instead of the sentinel empty value.
Capacity == meetingPlace = MeetingPlaceEmpty \/ meetingPlace \in Creatures

\* SAFETY properties come first in the .cfg file, so a mis-spelled name
\* here would silently drop the invariant rather than fail the build.
SpecOK == Spec /\ SumMet /\ Capacity

====