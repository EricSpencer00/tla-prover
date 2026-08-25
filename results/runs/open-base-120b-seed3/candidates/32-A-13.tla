---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    N,                \* number of creatures
    M,                \* total meetings limit
    Faded,            \* the faded color
    MeetingPlaceEmpty \* marker for an empty meeting place

\* ----------------------------------------------------------------------
\* Colors (including the faded color)
\* ----------------------------------------------------------------------
CONSTANTS Blue, Red, Yellow
ColorSet == {Blue, Red, Yellow, Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES cr, mall, total

\* ----------------------------------------------------------------------
\* Type definition for a creature's record
\* ----------------------------------------------------------------------
Creature == [color : ColorSet, meetings : Nat]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ cr = [i \in 1..N |-> 
                [color    |-> CHOOSE c \in {Blue, Red, Yellow} : TRUE,
                 meetings |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in {Blue, Red, Yellow} : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
         /\ cr[i].color # Faded
         /\ mall' = i
         /\ UNCHANGED <<cr, total>>

FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E i \in 1..N :
         /\ cr[i].color # Faded
         /\ cr' = [cr EXCEPT ![i].color = Faded]
         /\ UNCHANGED <<mall, total>>

MeetAndMutate ==
    /\ mall \in 1..N
    /\ total < M
    /\ \E a \in 1..N :
         /\ a # mall
         /\ cr[a].color # Faded
         /\ cr[mall].color # Faded
         /\ LET newColor == Complement(cr[a].color, cr[mall].color) IN
                /\ cr' = [cr EXCEPT 
                           ![a].color    = newColor,
                           ![a].meetings = @ + 1,
                           ![mall].color    = newColor,
                           ![mall].meetings = @ + 1]
                /\ total' = total + 1
                /\ mall' = MeetingPlaceEmpty

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<cr, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ cr \in [1..N -> Creature]
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M

SumMet ==
    (total = M) => (Sum({ cr[i].meetings : i \in 1..N }) = 2 * M)

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====