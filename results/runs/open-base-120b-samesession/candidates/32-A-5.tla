---- MODULE Chameneos ----
EXTENDS Naturals, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow", Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES creatures, mall, total

vars == <<creatures, mall, total>>

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CASE
      (c1 = "blue"  /\ c2 = "red")  \/ (c1 = "red"   /\ c2 = "blue")  -> "yellow" ;
      (c1 = "blue"  /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") -> "red"    ;
      (c1 = "red"   /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "red")  -> "blue"   ;
      OTHER -> c1 \* (should not occur)
    ENDCASE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ creatures = [i \in 1..N |-> [color |-> CHOOSE c \in {"blue","red","yellow"} : TRUE,
                                 count |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ total < M
  /\ mall = MeetingPlaceEmpty
  /\ \E i \in 1..N :
        /\ creatures[i].color # Faded
        /\ mall' = i
        /\ UNCHANGED <<creatures, total>>

FadeOut ==
  /\ total = M
  /\ mall = MeetingPlaceEmpty
  /\ \E i \in 1..N :
        /\ creatures[i].color # Faded
        /\ creatures' = [creatures EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<mall, total>>

Meet ==
  /\ total < M
  /\ mall # MeetingPlaceEmpty
  /\ \E i \in 1..N :
        /\ i # mall
        /\ creatures[i].color # Faded
        /\ creatures[mall].color # Faded
        LET newColor == Complement(creatures[i].color, creatures[mall].color) IN
          /\ creatures' = [creatures EXCEPT
                            ![i]     = [color |-> newColor, count |-> @.count + 1],
                            ![mall]  = [color |-> newColor, count |-> @.count + 1]]
          /\ total' = total + 1
          /\ mall' = MeetingPlaceEmpty

Next == \/ Enter \/ FadeOut \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ creatures \in [1..N -> [color: Color, count: Nat]]
  /\ mall \in {MeetingPlaceEmpty} \cup 1..N
  /\ total \in Nat
  /\ total <= M

\* ----------------------------------------------------------------------
\* Safety property: sum of individual meeting counts
\* ----------------------------------------------------------------------
SumMet ==
  (total = M) => (+/ i \in 1..N : creatures[i].count) = 2 * M

====