---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Color == {"Blue", "Red", "Yellow", Faded}
Blue   == "Blue"
Red    == "Red"
Yellow == "Yellow"

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Complement rule: if the two colors are the same, keep that color;
\* otherwise return the third color that is different from both.
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE IF (c1 = Blue  /\ c2 = Red)   \/ (c1 = Red   /\ c2 = Blue)   THEN Yellow
  ELSE IF (c1 = Red   /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red)   THEN Blue
  ELSE IF (c1 = Blue  /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) THEN Red
  ELSE Faded

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ creatures = [i \in 1..N |-> <<ChooseColor(i), 0>>]
  /\ mall      = MeetingPlaceEmpty
  /\ total     = 0

\* Choose a non‑faded initial color nondeterministically
ChooseColor(i) == CHOOSE c \in {"Blue", "Red", "Yellow"} : TRUE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ c \in 1..N
  /\ creatures[c][1] # Faded
  /\ mall' = c
  /\ UNCHANGED <<creatures, total>>

Fade ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ c \in 1..N
  /\ creatures[c][1] # Faded
  /\ creatures' = [creatures EXCEPT ![c] = <<Faded, creatures[c][2]>>]
  /\ UNCHANGED <<mall, total>>

Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ w = mall
  /\ c \in 1..N
  /\ c # w
  /\ creatures[c][1] # Faded
  /\ creatures[w][1] # Faded
  /\ total < M
  /\ newCol = Complement(creatures[c][1], creatures[w][1])
  /\ creatures' = [creatures EXCEPT 
        ![c] = <<newCol, creatures[c][2] + 1>>, 
        ![w] = <<newCol, creatures[w][2] + 1>>]
  /\ mall' = MeetingPlaceEmpty
  /\ total' = total + 1

Next ==
  \/ Enter
  \/ Fade
  \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<creatures, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ creatures \in [1..N -> Color \X Nat]
  /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  /\ total = M =>
       (\Sum i \in 1..N : creatures[i][2]) = 2 * M

\* ----------------------------------------------------------------------
\* Theorems / properties required by the .cfg file
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []SumMet

====