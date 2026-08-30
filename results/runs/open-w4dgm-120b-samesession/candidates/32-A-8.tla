---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature identifiers: 1..N. Colors: blue, red, yellow, plus the faded state.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Match(c, d) == IF c = d THEN c ELSE LET cs == {"blue", "red", "yellow"}
                                      In cs \ {c, d} IN CHOOSE e \in cs : TRUE

VARIABLES colorCount, waiting, totalMeetings

vars == <<colorCount, waiting, totalMeetings>>

TypeOK ==
    /\ colorCount \in [Creatures -> [color : Colors, count : 0..M]]
    /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ colorCount = [c \in Creatures |-> [color |-> CHOOSE d \in {"blue", "red", "yellow"} : TRUE,
                                          count |-> 0]]
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterEmptyMall(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ colorCount[c].color # Faded
    /\ totalMeetings < M
    /\ waiting' = c
    /\ UNCHANGED <<colorCount, totalMeetings>>

FadeOut(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ colorCount[c].color # Faded
    /\ colorCount' = [colorCount EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<waiting, totalMeetings>>

MeetAndMutate(c) ==
    /\ waiting # MeetingPlaceEmpty
    /\ waiting # c
    /\ totalMeetings < M
    /\ LET newcol == Match(colorCount[c].color, colorCount[waiting].color) IN
        /\ colorCount' = [colorCount EXCEPT
                            ![c] = [color |-> newcol, count |-> @.count + 1],
                            ![waiting] = [color |-> newcol, count |-> @.count + 1]]
    /\ waiting' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E c \in Creatures : EnterEmptyMall(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == (totalMeetings = M) => (2 * totalMeetings = colorCount[1].count + colorCount[2].count
                                    + IF N >= 3 THEN colorCount[3].count ELSE 0
                                    + IF N >= 4 THEN colorCount[4].count ELSE 0)

====