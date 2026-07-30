---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N >= 1 /\ M \in Nat /\ M >= 1

CREATURES == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}
StateColors == {"blue", "red", "yellow"}
Third(c1, c2) == IF {c1, c2} = {"blue", "red"} THEN "yellow"
                 ELSE IF {c1, c2} = {"blue", "yellow"} THEN "red"
                 ELSE IF {c1, c2} = {"red", "yellow"} THEN "blue"
                 ELSE c1

VARIABLES profile, waiting, meetings

vars == <<profile, waiting, meetings>>

RECURSIVE SumCount(_)
SumCount(S) ==
    IF S = {} THEN 0
    ELSE LET c == CHOOSE x \in S : TRUE IN profile[c][2] + SumCount(S \ {c})

TypeOK ==
    /\ profile \in [CREATURES -> [color : Colors, count : 0 .. M]]
    /\ waiting \in {MeetingPlaceEmpty} \cup CREATURES
    /\ meetings \in 0 .. M

Init ==
    /\ profile = [c \in CREATURES |->
                    [color |-> CHOOSE k \in StateColors : TRUE,
                     count |-> 0]]
    /\ waiting = MeetingPlaceEmpty
    /\ meetings = 0

Enter(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ meetings < M
    /\ profile[c].color # Faded
    /\ waiting' = c
    /\ UNCHANGED <<profile, meetings>>

Fade(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ meetings = M
    /\ profile[c].color # Faded
    /\ profile' = [profile EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<waiting, meetings>>

Meet(c) ==
    /\ waiting # MeetingPlaceEmpty
    /\ waiting # c
    /\ profile[c].color # Faded
    /\ profile[waiting].color # Faded
    /\ LET newcol == IF profile[c].color = profile[waiting].color
                     THEN profile[c].color
                     ELSE Third(profile[c].color, profile[waiting].color)
       IN profile' = [profile EXCEPT ![c].color = newcol,
                                   ![c].count = @ + 1,
                                   ![waiting].color = newcol,
                                   ![waiting].count = @ + 1]
    /\ meetings' = meetings + 1
    /\ waiting' = MeetingPlaceEmpty

Next ==
    \/ \E c \in CREATURES : Enter(c)
    \/ \E c \in CREATURES : Fade(c)
    \/ \E c \in CREATURES : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet == meetings = M => SumCount(CREATURES) = 2 * M

====