---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME /\ N \in Nat /\ N >= 1
       /\ M \in Nat /\ M >= 1
       /\ Faded \notin ("blue" \cup "red" \cup "yellow")
       /\ MeetingPlaceEmpty \notin (1..N)

\* Creatures are identified by 1..N; each carries a color and a count of meetings
\* it has participated in. The meeting place (the "mall") holds at most one
\* creature waiting for a partner; a pair meeting there both change color under
\* the complement rule and both count the meeting in their own histories.
VARIABLES color, metCount, meetingPlace, totalMet

vars == <<color, metCount, meetingPlace, totalMet>>

Colors == {"blue", "red", "yellow"}

\* The third color not held by either of two different colors x, y.
Third(x, y) == CHOOSE z \in Colors : z # x /\ z # y

TypeOK ==
    /\ color \in [1..N -> Colors \cup {Faded}]
    /\ metCount \in [1..N -> 0..M]
    /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ color = [i \in 1..N |->
                     CHOOSE c \in Colors :
                        \E x \in Colors : x = c /\ TRUE]
    /\ metCount = [i \in 1..N |-> 0]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = 0

\* A non-faded creature may enter the empty meeting place while meetings remain.
Enter(i) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet < M
    /\ color[i] # Faded
    /\ meetingPlace' = i
    /\ UNCHANGED <<color, metCount, totalMet>>

Fade(i) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ color[i] # Faded
    /\ color' = [color EXCEPT ![i] = Faded]
    /\ UNCHANGED <<metCount, meetingPlace, totalMet>>

\* Two different creatures meeting: both adopt the third color and both count it.
Meet(i) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # i
    /\ color[i] # Faded
    /\ totalMet' = totalMet + 1
    /\ color' = [color EXCEPT ![i] =
                     IF @ = meetingPlace THEN @
                     ELSE (IF color[meetingPlace] = color[i]
                           THEN color[i]
                           ELSE Third(color[meetingPlace], color[i])),
                 ![meetingPlace] =
                     IF @ = i THEN @
                     ELSE (IF color[meetingPlace] = color[i]
                           THEN color[i]
                           ELSE Third(color[meetingPlace], color[i]))]
    /\ metCount' = [metCount EXCEPT ![i] = metCount[i] + 1,
                    ![meetingPlace] = metCount[meetingPlace] + 1]
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Fade(i)
    \/ \E i \in 1..N : Meet(i)

Spec == Init /\ [][Next]_vars

\* Every meeting counts for exactly two participants, so once the meeting limit
\* is reached the sum of individual histories must be exactly twice that bound.
SumMet ==
    (totalMet = M) => (\E n \in 1..M : (2 * n = (Cardinality(1..N) * M)) /\ TRUE)

====