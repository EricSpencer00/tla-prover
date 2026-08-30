---- MODULE Chameneos ----
EXTENDS Integers, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}
NoColor == "none"

VARIABLES cstate, mall, total
vars == <<cstate, mall, total>>

RECURSIVE Tally(_)
Tally(S) == IF S = {} THEN 0
            ELSE LET c == CHOOSE x \in S : TRUE IN cstate[c][2] + Tally(S \ {c})

InitColor(c) == CHOOSE col \in {"blue", "red", "yellow"}
                     : TRUE

OtherColor(col, col2) ==
    IF col = col2 THEN col
    ELSE IF {col, col2} = {"blue", "red"} THEN "yellow"
    ELSE IF {col, col2} = {"blue", "yellow"} THEN "red"
    ELSE IF {col, col2} = {"red", "yellow"} THEN "blue"
    ELSE NoColor

TypeOK ==
    /\ cstate \in [Creatures -> (Colors \X (0 .. M))]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in 0 .. M

Init ==
    /\ cstate = [c \in Creatures |-> <<InitColor(c), 0>>]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

EnterEmpty(c) ==
    /\ cstate[c][1] # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ mall' = c
    /\ UNCHANGED <<cstate, total>>

FadeOut(c) ==
    /\ cstate[c][1] # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total >= M
    /\ cstate' = [cstate EXCEPT ![c] = <<Faded, cstate[c][2>>]
    /\ UNCHANGED <<mall, total>>

Meet(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ cstate[c][1] # Faded
    /\ total < M
    /\ LET col == OtherColor(cstate[c][1], cstate[mall][1]) IN
         /\ cstate' = [cstate EXCEPT ![c] = <<col, cstate[c][2] + 1>>,
                       ![mall] = <<col, cstate[mall][2] + 1>>]
    /\ total' = total + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterEmpty(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet ==
    (total = M) => (Tally(Creatures) = 2 * M)

====