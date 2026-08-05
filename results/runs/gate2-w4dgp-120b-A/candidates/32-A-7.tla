---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES color, meetingCount, meetingPlace, totalMet
vars == <<color, meetingCount, meetingPlace, totalMet>>

Colors == {1, 2, 3, Faded}
Meetings == 1 .. N

TypeOK ==
    /\ color \in [Meetings -> Colors]
    /\ meetingCount \in [Meetings -> 0 .. M]
    /\ meetingPlace \in Meetings \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0 .. M

\* The global meeting counter is the sum of the per-creature meeting counts:
\* each meeting contributed exactly two participations.
SumMeetings ==
    LET g[S \in SUBSET Meetings] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN meetingCount[x] + g[S \ {x}]
    IN g[Meetings]

Init ==
    /\ color \in [Meetings -> {1, 2, 3}]
    /\ meetingCount = [c \in Meetings |-> 0]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = 0

\* The complement rule: "same keeps same, otherwise both become the third".
Third(a, b) ==
    IF a = b THEN a
    ELSE LET s == {1, 2, 3} \ {a, b} IN CHOOSE x \in s : TRUE

Enter(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet < M
    /\ color[c] # Faded
    /\ meetingPlace' = c
    /\ UNCHANGED <<color, meetingCount, totalMet>>

Fade(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = M
    /\ color[c] # Faded
    /\ color' = [color EXCEPT ![c] = Faded]
    /\ UNCHANGED <<meetingCount, meetingPlace, totalMet>>

Meet(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ color[c] # Faded
    /\ meetingCount[c] < M
    /\ meetingCount[meetingPlace] < M
    /\ color' = [color EXCEPT ![c] = Third(@, color[meetingPlace]), ![meetingPlace] = Third(@, color[c])]
    /\ meetingCount' = [meetingCount EXCEPT ![c] = @ + 1, ![meetingPlace] = @ + 1]
    /\ totalMet' = totalMet + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next == \E c \in Meetings : Enter(c) \/ Fade(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* Once the meeting place has closed, the total meetings recorded must account
\* for every creature's individual participation.
SumMet == (totalMet = M) => (SumMeetings = 2 * M)

====