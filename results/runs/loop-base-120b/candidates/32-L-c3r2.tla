---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N          \* number of creatures
CONSTANT M          \* total meetings limit
CONSTANT Faded      \* value representing a faded creature
CONSTANT MeetingPlaceEmpty \* value representing an empty meeting place

\* ----- Sets and derived constants -----
Creatures == 1..N
BaseColors == {"blue", "red", "yellow"}
Colors == BaseColors \cup {Faded}

\* ----- State variables -----
VARIABLES colCount, place, g

\* ----- Helper function: complement rule -----
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in BaseColors :
      /\ c # c1
      /\ c # c2

\* ----- Initial state -----
Init ==
  /\ place = MeetingPlaceEmpty
  /\ g = 0
  /\ \A c \in Creatures :
        colCount[c] = [ color   |-> CHOOSE col \in BaseColors : TRUE,
                       meetings |-> 0 ]

\* ----- Action: a non‑faded creature enters an empty meeting place -----
Enter ==
  \E c \in Creatures :
    /\ colCount[c].color # Faded
    /\ place = MeetingPlaceEmpty
    /\ g < M
    /\ place' = c
    /\ UNCHANGED << colCount, g >>

\* ----- Action: a creature fades out when the limit has been reached -----
Fade ==
  \E c \in Creatures :
    /\ colCount[c].color # Faded
    /\ place = MeetingPlaceEmpty
    /\ g = M
    /\ colCount' = [colCount EXCEPT ![c].color = Faded]
    /\ UNCHANGED << place, g >>

\* ----- Action: two different creatures meet and mutate -----
Meet ==
  \E c \in Creatures :
    LET p == place IN
      /\ p # MeetingPlaceEmpty
      /\ c # p
      /\ colCount[c].color # Faded
      /\ colCount[p].color # Faded
      /\ g < M
      /\ LET newCol == Complement(colCount[c].color, colCount[p].color) IN
           colCount' = [colCount EXCEPT
                          ![c] = [color |-> newCol,
                                 meetings |-> colCount[c].meetings + 1],
                          ![p] = [color |-> newCol,
                                 meetings |-> colCount[p].meetings + 1]]
      /\ place' = MeetingPlaceEmpty
      /\ g' = g + 1
      /\ UNCHANGED << >>

\* ----- Next-state relation -----
Next == Enter \/ Fade \/ Meet

\* ----- Variables tuple for the temporal operator -----
vars == << colCount, place, g >>

\* ----- Specification -----
Spec == Init /\ [][Next]_vars

\* ----- Type correctness invariant -----
TypeOK ==
  /\ colCount \in [Creatures -> [color: Colors, meetings: Nat]]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ g \in Nat

\* ----- Safety invariant: sum of individual meeting counts -----
SumMet ==
  (g = M) => ((\Sum c \in Creatures : colCount[c].meetings) = 2 * M)

\* ----- List of invariants for the model checker -----
INVARIANTS == TypeOK /\ SumMet

====