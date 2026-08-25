---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES c, place, total

\* ----------------------------------------------------------------------
\* Sets and derived constants
\* ----------------------------------------------------------------------
Creatures == 1..N
Colors    == {"blue", "red", "yellow", Faded}

\* ----------------------------------------------------------------------
\* Complement rule for two colors
\* ----------------------------------------------------------------------
Complement(col1, col2) ==
  CASE
    col1 = col2 -> col1
    [] (col1 = "blue" /\ col2 = "red") \/ (col1 = "red" /\ col2 = "blue") -> "yellow"
    [] (col1 = "blue" /\ col2 = "yellow") \/ (col1 = "yellow" /\ col2 = "blue") -> "red"
    [] (col1 = "red" /\ col2 = "yellow") \/ (col1 = "yellow" /\ col2 = "red") -> "blue"
    [] TRUE -> Faded

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ c = [i \in Creatures |-> 
            [col |-> CHOOSE col \in {"blue","red","yellow"} : col,
             met |-> 0]]
  /\ place = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  \E i \in Creatures :
    /\ c[i].col # Faded
    /\ place = MeetingPlaceEmpty
    /\ total < M
    /\ place' = i
    /\ UNCHANGED <<c, total>>

FadeOut ==
  \E i \in Creatures :
    /\ c[i].col # Faded
    /\ place = MeetingPlaceEmpty
    /\ total = M
    /\ c' = [c EXCEPT ![i].col = Faded]
    /\ UNCHANGED total
    /\ place' = MeetingPlaceEmpty

Meet ==
  \E i \in Creatures, p \in Creatures :
    /\ place = p
    /\ i # p
    /\ c[i].col # Faded
    /\ c[p].col # Faded
    /\ total < M
    /\ LET newcol == Complement(c[i].col, c[p].col) IN
         /\ c' = [c EXCEPT
                  ![i] = [c[i] EXCEPT !.col = newcol, !.met = @ + 1],
                  ![p] = [c[p] EXCEPT !.col = newcol, !.met = @ + 1]]
         /\ total' = total + 1
         /\ place' = MeetingPlaceEmpty

Next == Enter \/ FadeOut \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<c, place, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ c \in [Creatures -> [col : Colors, met : Nat]]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  total = M => 
    LET sum == Sum({ i \in Creatures : c[i].met })
    IN sum = 2 * M

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* (constants N, M, Faded, MeetingPlaceEmpty are already declared)
\* (Spec is the specification formula)
\* (TypeOK, SumMet are the invariants)

====