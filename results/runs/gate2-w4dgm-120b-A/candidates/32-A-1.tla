---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

\* The complement rule: given two colors, the result is the third color
\* in the set when they differ, and that same color when they match.
COMPLEMENT(c1, c2) == IF c1 = c2 THEN c1
                      ELSE LET k == {"blue", "red", "yellow"} IN (k \ {c1, c2}) \notempty

VARIABLES cmap, meetingPlace, totalMeetings

vars == <<cmap, meetingPlace, totalMeetings>>

TypeOK ==
    /\ cmap \in [Creatures -> (Colors \X (0..M))]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ cmap \in [Creatures -> (Colors \ {Faded}) \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterPlace ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ \E c \in Creatures :
        /\ cmap[c][1] # Faded
        /\ meetingPlace' = c
    /\ UNCHANGED <<cmap, totalMeetings>>

FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ \E c \in Creatures :
        /\ cmap[c][1] # Faded
        /\ cmap' = [cmap EXCEPT ![c][1] = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* The arriving creature must be different from the one waiting in the place.
MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ \E c \in Creatures :
        /\ meetingPlace # c
        /\ cmap[meetingPlace][1] # Faded
        /\ cmap[c][1] # Faded
        /\ cmap' = [cmap EXCEPT ![c] = <<COMPLEMENT(cmap[c][1], cmap[meetingPlace][1]), cmap[c][2] + 1>>,
                               ![meetingPlace] = <<COMPLEMENT(cmap[c][1], cmap[meetingPlace][1]), cmap[meetingPlace][2] + 1>>]
    /\ totalMeetings' = totalMeetings + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next == EnterPlace \/ FadeOut \/ MeetAndMutate

Spec == Init /\ [][Next]_vars

SumMet == totalMeetings = M => (LET total == (c1, c2) \in Creatures : cmap[c1][2] + cmap[c2][2] IN total = 2 * M)

====