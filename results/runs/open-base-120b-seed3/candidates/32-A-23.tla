---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Blue   == "blue"
Red    == "red"
Yellow == "yellow"

BasicColors == {Blue, Red, Yellow}
Color == BasicColors \cup {Faded}

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    CASE 
      (c1 = Blue  /\ c2 = Red)   \/ (c1 = Red   /\ c2 = Blue)   -> Yellow ;
      (c1 = Blue  /\ c2 = Yellow)\/ (c1 = Yellow\/ c2 = Blue) -> Red    ;
      (c1 = Red   /\ c2 = Yellow)\/ (c1 = Yellow\/ c2 = Red)   -> Blue   ;
      OTHER -> Faded \* should never occur
    END

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES creatures, mall, total

\* creatures : [1..N -> <<color, count>>]
\* mall      : either a creature id (1..N) or MeetingPlaceEmpty
\* total     : total number of completed meetings

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  \E initColors \in [1..N -> BasicColors] :
    /\ creatures = [c \in 1..N |-> <<initColors[c], 0>>]
    /\ mall      = MeetingPlaceEmpty
    /\ total     = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in 1..N :
        /\ creatures[c][1] # Faded
        /\ mall' = c
        /\ UNCHANGED <<creatures, total>>

Fade ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ \E c \in 1..N :
        /\ creatures[c][1] # Faded
        /\ creatures' = [creatures EXCEPT ![c] = <<Faded, creatures[c][2>>]]
        /\ UNCHANGED <<mall, total>>

Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E c2 \in 1..N :
        LET c1 == mall IN
        /\ c2 # c1
        /\ creatures[c1][1] # Faded
        /\ creatures[c2][1] # Faded
        /\ LET newCol == Complement(creatures[c1][1], creatures[c2][1]) IN
           /\ creatures' = [creatures EXCEPT
                               ![c1] = <<newCol, creatures[c1][2] + 1>>,
                               ![c2] = <<newCol, creatures[c2][2] + 1>>]
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
  /\ creatures \in [1..N -> [color : Color, count : Nat]]
  /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

SumMet ==
  total = M => ( \SUM c \in 1..N : creatures[c][2] ) = 2 * M

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* SPECIFICATION   := Spec
\* INVARIANTS      := TypeOK, SumMet
=============================================================================