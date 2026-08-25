---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Sets and derived constants
\* ----------------------------------------------------------------------
Creatures == 1..N
Blue == "blue"
Red  == "red"
Yellow == "yellow"
ColorSet == {Blue, Red, Yellow}
AllColors == ColorSet \cup {Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES cmap, mall, total

\* cmap : mapping each creature to a record [color : AllColors, cnt : Nat]
\* mall : either MeetingPlaceEmpty or a creature identifier
\* total: total number of completed meetings

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in ColorSet : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ cmap \in [Creatures -> [color : ColorSet, cnt : Nat]]
    /\ \A i \in Creatures: cmap[i].cnt = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in Creatures :
          /\ cmap[i].color # Faded
          /\ i # MeetingPlaceEmpty
          /\ mall' = i
          /\ cmap' = cmap
          /\ total' = total

FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total >= M
    /\ \E i \in Creatures :
          /\ cmap[i].color # Faded
          /\ mall' = MeetingPlaceEmpty
          /\ cmap' = [cmap EXCEPT ![i].color = Faded]
          /\ total' = total

MeetAndMutate ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E j \in Creatures :
          /\ j # mall
          /\ cmap[mall].color # Faded
          /\ cmap[j].color # Faded
          /\ LET newCol == Complement(cmap[mall].color, cmap[j].color) IN
                /\ cmap' = [cmap EXCEPT
                              ![mall].color = newCol,
                              ![mall].cnt   = @ + 1,
                              ![j].color    = newCol,
                              ![j].cnt      = @ + 1]
                /\ mall' = MeetingPlaceEmpty
                /\ total' = total + 1

Next ==
    \/ Enter
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<cmap, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ cmap \in [Creatures -> [color : AllColors, cnt : Nat]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat

SumMet ==
    total = M => ( \Sum i \in Creatures : cmap[i].cnt ) = 2 * M

\* ----------------------------------------------------------------------
\* The set of invariants required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANT TypeOK
INVARIANT SumMet

====