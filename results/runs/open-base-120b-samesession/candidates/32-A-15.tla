---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

\*-----------------------------------------------------------------
\* CONSTANTS (to be instantiated in the .cfg file)
\*-----------------------------------------------------------------
CONSTANT N            \* number of creatures
CONSTANT M            \* total meetings limit
CONSTANT Faded        \* token representing the faded color
CONSTANT MeetingPlaceEmpty  \* token representing an empty meeting place

\*-----------------------------------------------------------------
\* BASIC SETS
\*-----------------------------------------------------------------
ActiveColors == {"blue", "red", "yellow"}
ColorSet     == ActiveColors \cup {Faded}

\*-----------------------------------------------------------------
\* STATE VARIABLES
\*-----------------------------------------------------------------
VARIABLES creatures, mall, total

\* creatures : [1..N -> [color : ColorSet, meetings : Nat]]
\* mall      : either MeetingPlaceEmpty or an identifier in 1..N
\* total     : Nat, number of completed meetings

\*-----------------------------------------------------------------
\* COMPLEMENT RULE
\*-----------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in ActiveColors : c # c1 /\ c # c2

\*-----------------------------------------------------------------
\* INITIAL STATE
\*-----------------------------------------------------------------
Init ==
  /\ \E colFun \in [1..N -> ActiveColors] :
        /\ creatures = [i \in 1..N |-> [color |-> colFun[i],
                                      meetings |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\*-----------------------------------------------------------------
\* ACTION: ENTER EMPTY MEETING PLACE
\*-----------------------------------------------------------------
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in 1..N :
        /\ creatures[c].color # Faded
        /\ mall' = c
        /\ creatures' = creatures
        /\ total' = total

\*-----------------------------------------------------------------
\* ACTION: FADE OUT (when the mall is closed)
\*-----------------------------------------------------------------
Fade ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ \E c \in 1..N :
        /\ creatures[c].color # Faded
        /\ mall' = MeetingPlaceEmpty
        /\ creatures' = [creatures EXCEPT ![c] = [color |-> Faded,
                                                meetings |-> @.meetings]]
        /\ total' = total

\*-----------------------------------------------------------------
\* ACTION: MEET AND MUTATE
\*-----------------------------------------------------------------
Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in 1..N :
        /\ c # mall
        /\ creatures[c].color # Faded
        /\ creatures[mall].color # Faded
        /\ LET w == mall IN
           LET newcol == Complement(creatures[c].color, creatures[w].color) IN
             /\ mall' = MeetingPlaceEmpty
             /\ total' = total + 1
             /\ creatures' = [creatures EXCEPT
                                 ![c] = [color |-> newcol,
                                         meetings |-> @.meetings + 1],
                                 ![w] = [color |-> newcol,
                                         meetings |-> @.meetings + 1]]

\*-----------------------------------------------------------------
\* NEXT STATE RELATION
\*-----------------------------------------------------------------
Next == Enter \/ Fade \/ Meet

\*-----------------------------------------------------------------
\* TYPE INVARIANT
\*-----------------------------------------------------------------
TypeOK ==
  /\ creatures \in [1..N -> [color : ColorSet, meetings : Nat]]
  /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

\*-----------------------------------------------------------------
\* SAFETY INVARIANT: SUM OF INDIVIDUAL COUNTS
\*-----------------------------------------------------------------
SumMet ==
  total = M => 
    LET sum == +/ c \in 1..N : creatures[c].meetings IN
      sum = 2 * M

\*-----------------------------------------------------------------
\* SPECIFICATION
\*-----------------------------------------------------------------
vars == <<creatures, mall, total>>

Spec == Init /\ [][Next]_vars

\*-----------------------------------------------------------------
\* THE REQUIRED IDENTIFIERS
\*-----------------------------------------------------------------
INVARIANT TypeOK
INVARIANT SumMet

====