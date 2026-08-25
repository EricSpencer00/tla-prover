---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Sets and constants
\* ----------------------------------------------------------------------
Creatures == 1 .. N

Blue == "blue"
Red  == "red"
Yellow == "yellow"

PrimaryColors == {Blue, Red, Yellow}
ColorSet == PrimaryColors \cup {Faded}

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in PrimaryColors : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES cre, place, total

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ cre \in [Creatures -> [color : ColorSet, meetCount : Nat]]
    /\ place \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ cre \in [Creatures -> [color : PrimaryColors, meetCount : Nat]]
    /\ \A c \in Creatures : cre[c].meetCount = 0
    /\ place = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    \E c \in Creatures :
        /\ place = MeetingPlaceEmpty
        /\ total < M
        /\ cre[c].color # Faded
        /\ place' = c
        /\ UNCHANGED <<cre, total>>

FadeOut ==
    \E c \in Creatures :
        /\ place = MeetingPlaceEmpty
        /\ total = M
        /\ cre[c].color # Faded
        /\ cre' = [cre EXCEPT ![c].color = Faded]
        /\ UNCHANGED <<place, total>>

Meet ==
    \E c \in Creatures :
        /\ place # MeetingPlaceEmpty
        /\ c # place
        /\ total < M
        /\ cre[c].color # Faded
        /\ cre[place].color # Faded
        /\ LET newcol == Complement(cre[c].color, cre[place].color) IN
             /\ cre' = [cre EXCEPT
                        ![c] = [color |-> newcol,
                                meetCount |-> cre[c].meetCount + 1],
                        ![place] = [color |-> newcol,
                                    meetCount |-> cre[place].meetCount + 1]]
             /\ total' = total + 1
             /\ place' = MeetingPlaceEmpty

Next == \/ Enter \/ FadeOut \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<cre, place, total>>

\* ----------------------------------------------------------------------
\* Safety property: sum of individual meeting counts
\* ----------------------------------------------------------------------
SumMet ==
    total = M => 
        Sum({ cre[c].meetCount : c \in Creatures }) = 2 * M

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* SPECIFICATION:
SPECIFICATION Spec

\* INVARIANTS:
INVARIANT TypeOK
INVARIANT SumMet

====