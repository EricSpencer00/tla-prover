---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Sets and derived constants
\* ----------------------------------------------------------------------
Creatures == 1..N
ColorSet  == {"blue", "red", "yellow"}
AllColors == ColorSet ∪ {Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES state, mall, gcount

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE 
    CASE 
      (c1 = "blue"  /\ c2 = "red")    \/ (c1 = "red"    /\ c2 = "blue")    -> "yellow" ;
      (c1 = "blue"  /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue")   -> "red" ;
      (c1 = "red"   /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "red")    -> "blue"
    END

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state = [c \in Creatures |-> 
                [color |-> CHOOSE col \in ColorSet : TRUE,
                 meetCount |-> 0]]
  /\ mall   = MeetingPlaceEmpty
  /\ gcount = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ gcount < M
  /\ \E c \in Creatures :
        /\ state[c].color # Faded
        /\ mall' = c
        /\ UNCHANGED << state, gcount >>

FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ gcount = M
  /\ \E c \in Creatures :
        /\ state[c].color # Faded
        /\ state' = [state EXCEPT ![c].color = Faded]
        /\ UNCHANGED << mall, gcount >>

Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ \E c \in Creatures :
        /\ c # mall
        /\ state[c].color # Faded
        /\ state[mall].color # Faded
        /\ LET col1   == state[c].color ;
               col2   == state[mall].color ;
               newcol == Complement(col1, col2)
           IN
              /\ state' = [state EXCEPT 
                            ![c].color        = newcol,
                            ![c].meetCount    = @ + 1,
                            ![mall].color     = newcol,
                            ![mall].meetCount = @ + 1]
              /\ mall'   = MeetingPlaceEmpty
              /\ gcount' = gcount + 1

Next == \/ Enter \/ FadeOut \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mall, gcount>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [Creatures -> [color : AllColors, meetCount : Nat]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ gcount \in Nat
  /\ gcount <= M

SumMet ==
  (gcount = M) => (Sum({ state[c].meetCount : c \in Creatures }) = 2 * M)

====