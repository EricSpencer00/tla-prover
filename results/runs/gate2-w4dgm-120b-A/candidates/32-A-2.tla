---- MODULE Chameneos ----
EXTENDS Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}

\* The complement rule behind the meeting: the two creatures leave holding the
\* third color in the set if they started different, and keep their color if
\* they started the same.
Complement(c, c) == c
Complement("blue", "red")    == "yellow"
Complement("red", "blue")    == "yellow"
Complement("blue", "yellow") == "red"
Complement("yellow", "blue") == "red"
Complement("red", "yellow")  == "blue"
Complement("yellow", "red")  == "blue"

SumCounts(ch) == LET g[S \in SUBSET Creatures] ==
                    IF S = {} THEN 0
                    ELSE LET x == CHOOSE y \in S : TRUE
                         IN ch[x][2] + g[S \ {x}]
                IN g[Creatures]

VARIABLES state, place, total.

vars == <<state, place, total>>

TypeOK ==
    /\ state \in [Creatures -> (Colors \X (0 .. M))]
    /\ place \in (Creatures \cup {MeetingPlaceEmpty})
    /\ total \in 0 .. M

Init ==
    /\ state \in [Creatures -> (Colors \ {Faded} \X {0})]
    /\ place = MeetingPlaceEmpty
    /\ total = 0

EnterPlace(x) ==
    /\ place = MeetingPlaceEmpty
    /\ state[x][1] # Faded
    /\ total < M
    /\ place' = x
    /\ UNCHANGED <<state, total>>

Fade(x) ==
    /\ place = MeetingPlaceEmpty
    /\ total = M
    /\ state[x][1] # Faded
    /\ state' = [state EXCEPT ![x] = <<Faded, state[x][2]>>]
    /\ UNCHANGED <<place, total>>

\* The meeting: both participants adopt a mutually consistent new color.
Meet(x) ==
    /\ place # MeetingPlaceEmpty
    /\ place # x
    /\ state[x][1] # Faded
    /\ total < M
    /\ LET newcol == Complement(state[x][1], state[place][1]) IN
         /\ state' = [state EXCEPT ![x] = <<newcol, state[x][2] + 1>>,
                               ![place] = <<newcol, state[place][2] + 1>>]
    /\ total' = total + 1
    /\ place' = MeetingPlaceEmpty

Next ==
    \/ \E x \in Creatures : EnterPlace(x)
    \/ \E x \in Creatures : Fade(x)
    \/ \E x \in Creatures : Meet(x)

Spec == Init /\ [][Next]_vars

SumMet == total = M => SumCounts(state) = 2 * M

TypeOKInv == TypeOK

====