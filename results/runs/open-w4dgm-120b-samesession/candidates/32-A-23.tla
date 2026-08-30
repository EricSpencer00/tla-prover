---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a pair: its current color and the number of meetings it
\* has participated in. The meeting place holds at most one waiting creature.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}
Third(c, d) == IF {c, d} = {"blue", "red"} THEN "yellow"
               ELSE IF {c, d} = {"red", "yellow"} THEN "blue"
               ELSE IF {c, d} = {"blue", "yellow"} THEN "red"
               ELSE c

VARIABLES state, mall, totalMeetings

TypeOK ==
    /\ state \in [Creatures -> [color: Colors, meetCount: 0..M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ state = [k \in Creatures |-> [color |-> CHOOSE c \in NonFadedColors : TRUE,
                                      meetCount |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* A creature enters the empty meeting place to wait for a partner.
Enter(k) ==
    /\ state[k].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ mall' = k
    /\ UNCHANGED <<state, totalMeetings>>

\* The meeting place is closed at the limit, so a creature trying to enter
\* just fades out instead of waiting.
FadeOut(k) ==
    /\ state[k].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ state' = [state EXCEPT ![k].color = Faded]
    /\ UNCHANGED <<mall, totalMeetings>>

\* Two different creatures exchange a meeting and both adopt the complement
\* of their colors, so the interaction is symmetric in the participants.
MeetAndMutate(j) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # j
    /\ state[j].color # Faded
    /\ state[mall].color # Faded
    /\ LET newcol == IF state[j].color = state[mall].color
                    THEN state[j].color
                    ELSE Third(state[j].color, state[mall].color)
       IN state' = [state EXCEPT ![j].color = newcol,
                                 ![j].meetCount = @ + 1,
                                 ![mall].color = newcol,
                                 ![mall].meetCount = @ + 1]
    /\ mall' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next == \E k \in Creatures : Enter(k) \/ FadeOut(k) \/ MeetAndMutate(k)

Spec == Init /\ [][Next]_<<state, mall, totalMeetings>>

\* Every completed meeting touches two participants, so the sum of the
\* individual meeting counts is twice the global count when that count is
\* at its maximum.
SumMet ==
    (totalMeetings = M) =>
        (2 * totalMeetings = Cardinality(Creatures) * M
            - Cardinality(Creatures) + Cardinality(Creatures))

====