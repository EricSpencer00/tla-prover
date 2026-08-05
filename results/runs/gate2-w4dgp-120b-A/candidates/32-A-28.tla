---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* N creatures sit around one shared meeting place ("the mall").  Creatures pairwise
\* meet there, and each meeting is a two-sided handshake: the two participants each
\* record a meeting (+1 to their own count) and the whole system records one meeting
\* (the global counter).  Because a meeting always touches two participants, the sum
\* of individual counts always equals twice the number of completed meetings.  Once
\* the meeting limit M is reached the place closes, so entering it fades the creature.

Chameleons == {"ch1", "ch2", "ch3"}
Colors == {"blue", "red", "yellow", Faded}

VARIABLES color, metCount, totalMeetings, spot

vars == <<color, metCount, totalMeetings, spot>>

TypeOK ==
    /\ color \in [Chameleons -> Colors]
    /\ metCount \in [Chameleons -> 0..M]
    /\ totalMeetings \in 0..M
    /\ spot \in Chameleons \cup {MeetingPlaceEmpty}

Init ==
    /\ color \in [Chameleons -> {"blue", "red", "yellow"}]
    /\ metCount = [c \in Chameleons |-> 0]
    /\ totalMeetings = 0
    /\ spot = MeetingPlaceEmpty

\* A non-faded creature steps into the empty meeting place (if meetings are still
\* available).
Enter(c) ==
    /\ spot = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ color[c] # Faded
    /\ spot' = c
    /\ UNCHANGED <<color, metCount, totalMeetings>>

\* With the place closed, a creature that tries to enter instead fades.
Fade(c) ==
    /\ spot = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ color[c] # Faded
    /\ color' = [color EXCEPT ![c] = Faded]
    /\ UNCHANGED <<metCount, totalMeetings, spot>>

\* Two different creatures meet: both take the complement of their combined colors,
\* both record the meeting, and the place empties.
Complement(c1, c2) ==
    IF (c1 = c2 \/ (c1 = "blue" /\ c2 = "red") \/ (c1 = "red" /\ c2 = "blue"))
        THEN "yellow"
    ELSE IF (c1 = "red" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "red")
        THEN "blue"
    ELSE IF (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue")
        THEN "red"
    ELSE IF (c1 = "blue" /\ c2 = "blue") \/ (c1 = "red" /\ c2 = "red")
        THEN c1
    ELSE Faded

Meet(c) ==
    /\ spot # MeetingPlaceEmpty
    /\ spot # c
    /\ color' = [color EXCEPT ![spot] = Complement(color[spot], color[c]),
                               ![c]     = Complement(color[spot], color[c])]
    /\ metCount' = [metCount EXCEPT ![spot] = @ + 1, ![c] = @ + 1]
    /\ totalMeetings' = totalMeetings + 1
    /\ spot' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Chameleons : Enter(c)
    \/ \E c \in Chameleons : Fade(c)
    \/ \E c \in Chameleons : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet ==
    (totalMeetings = M) => (metCount["ch1"] + metCount["ch2"] + metCount["ch3"] = 2 * totalMeetings)

====