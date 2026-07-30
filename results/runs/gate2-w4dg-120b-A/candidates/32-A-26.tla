---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow"}
Complement(c1, c2) == IF c1 = c2 THEN c1 ELSE CHOOSE c \in Colors : c # c1 /\ c # c2

VARIABLES colorAndCount, place, total
vars == <<colorAndCount, place, total>>

RECURSIVE SumCounts(_)
SumCounts(S) == IF S = {} THEN 0
                ELSE LET x == CHOOSE y \in S : TRUE IN colorAndCount[x][2] + SumCounts(S \ {x})

Init ==
    /\ colorAndCount = [c \in Creatures |-> <<CHOOSE k \in Colors : TRUE, 0>>]
    /\ place = MeetingPlaceEmpty
    /\ total = 0

Enter(c) ==
    /\ place = MeetingPlaceEmpty
    /\ total < M
    /\ colorAndCount[c][1] # Faded
    /\ place' = c
    /\ UNCHANGED <<colorAndCount, total>>

Fade(c) ==
    /\ place = MeetingPlaceEmpty
    /\ total = M
    /\ colorAndCount[c][1] # Faded
    /\ colorAndCount' = [colorAndCount EXCEPT ![c] = <<Faded, colorAndCount[c][2>>]
    /\ UNCHANGED <<place, total>>

Meet(c) ==
    /\ place # MeetingPlaceEmpty
    /\ place # c
    /\ colorAndCount[c][1] # Faded
    /\ LET nc == Complement(colorAndCount[c][1], colorAndCount[place][1]) IN
         colorAndCount' = [colorAndCount EXCEPT ![c] = <<nc, colorAndCount[c][2] + 1>>,
                                           ![place] = <<nc, colorAndCount[place][2] + 1>>]
    /\ total' = total + 1
    /\ place' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : Fade(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ colorAndCount \in [Creatures -> (Colors \cup {Faded}) \X (0 .. M)]
    /\ place \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in 0 .. M

SumMet ==
    (total = M) => (SumCounts(Creatures) = 2 * M)

====