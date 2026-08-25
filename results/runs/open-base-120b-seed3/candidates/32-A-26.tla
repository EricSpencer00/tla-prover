---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty
CONSTANT  Blue, Red, Yellow

VARIABLES creatures, mall, total

\* ----------------------------------------------------------------------
\* Sets and Types
\* ----------------------------------------------------------------------
CreaturesSet == 1..N
Color == {Blue, Red, Yellow, Faded}

\* Complement rule for two colors
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF (c1 = Blue /\ c2 = Red) \/ (c1 = Red /\ c2 = Blue) THEN Yellow
    ELSE IF (c1 = Blue /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) THEN Red
    ELSE IF (c1 = Red /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red) THEN Blue
    ELSE Faded

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ creatures = [c \in CreaturesSet |-> <<CHOOSE col \in {Blue, Red, Yellow} : TRUE, 0>>]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    /\ total < M
    /\ mall = MeetingPlaceEmpty
    /\ \E c \in CreaturesSet :
         /\ creatures[c][1] # Faded
         /\ mall' = c
         /\ UNCHANGED <<creatures, total>>

Fade ==
    /\ total >= M
    /\ mall = MeetingPlaceEmpty
    /\ \E c \in CreaturesSet :
         /\ creatures[c][1] # Faded
         /\ creatures' = [creatures EXCEPT ![c] = <<Faded, creatures[c][2]>>]
         /\ UNCHANGED <<mall, total>>

Meet ==
    /\ total < M
    /\ mall # MeetingPlaceEmpty
    /\ \E c \in CreaturesSet :
         /\ c # mall
         /\ creatures[c][1] # Faded
         /\ LET w == mall;
                newCol == Complement(creatures[c][1], creatures[w][1])
            IN
            /\ creatures' = [creatures EXCEPT
                               ![c] = <<newCol, creatures[c][2] + 1>>,
                               ![w] = <<newCol, creatures[w][2] + 1>>]
            /\ total' = total + 1
            /\ mall' = MeetingPlaceEmpty

Next == Enter \/ Fade \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<creatures, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ creatures \in [CreaturesSet -> Color \X Nat]
    /\ mall \in CreaturesSet \cup {MeetingPlaceEmpty}
    /\ total \in Nat

SumMet ==
    total = M => Sum(i \in CreaturesSet: creatures[i][2]) = 2 * M

====