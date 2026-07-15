---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* the special faded color
    MeetingPlaceEmpty \* the value representing an empty meeting place

\* ----------------------------------------------------------------------
\* Enumerated set of base colors (excluding the faded color)
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow"}

\* ----------------------------------------------------------------------
\* Creatures set
\* ----------------------------------------------------------------------
Creatures == 1..N

\* ----------------------------------------------------------------------
\* State variables
\*   colMap : mapping each creature to its current color
\*   cntMap : mapping each creature to its personal meeting count
\*   mall   : current occupant of the meeting place (or MeetingPlaceEmpty)
\*   total  : global meeting counter
\* ----------------------------------------------------------------------
VARIABLES colMap, cntMap, mall, total

\* ----------------------------------------------------------------------
\* Initial state
\*   - each creature gets an arbitrary base color
\*   - each creature's meeting count is zero
\*   - meeting place is empty
\*   - total meetings is zero
\* ----------------------------------------------------------------------
Init ==
    /\ colMap = [c \in Creatures |-> CHOOSE col \in Colors : TRUE]
    /\ cntMap = [c \in Creatures |-> 0]
    /\ mall   = MeetingPlaceEmpty
    /\ total  = 0

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NonFaded(c) == colMap[c] # Faded
OtherColor(c1, c2) == CHOOSE col \in Colors : col # colMap[c1] /\ col # colMap[c2]

\* Complement rule for two colors
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE OtherColor(c1, c2)

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
        /\ NonFaded(c)
        /\ mall' = c
        /\ UNCHANGED <<colMap, cntMap, total>>

FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total >= M
    /\ \E c \in Creatures :
        /\ NonFaded(c)
        /\ colMap' = [colMap EXCEPT ![c] = Faded]
        /\ UNCHANGED <<cntMap, mall, total>>

MeetAndMutate ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
        /\ NonFaded(c)
        /\ c # mall
        /\ LET newCol == Complement(colMap[c], colMap[mall]) IN
           /\ colMap' = [colMap EXCEPT ![c] = newCol,
                                   ![mall] = newCol]
        /\ cntMap' = [cntMap EXCEPT ![c] = @ + 1,
                                   ![mall] = @ + 1]
        /\ total' = total + 1
        /\ mall' = MeetingPlaceEmpty
        /\ UNCHANGED <<>>

\* No other state changes are allowed
Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colMap, cntMap, mall, total>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures variables stay within intended domains)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ colMap \in [Creatures -> (Colors \cup {Faded})]
    /\ cntMap \in [Creatures -> Nat]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: when total meetings reach the limit,
\* the sum of all individual meeting counts equals twice the limit
\* ----------------------------------------------------------------------
SumMet ==
    (total = M) => ( \A c \in Creatures : cntMap[c] \in Nat ) /\
    (total = M) => ( Sum({cntMap[c] : c \in Creatures}) = 2 * M)

====