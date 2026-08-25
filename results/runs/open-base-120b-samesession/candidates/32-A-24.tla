---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ---------------------------------------------------------------------- *)
(* Colors *)
Blue   == "blue"
Red    == "red"
Yellow == "yellow"
Colors == {Blue, Red, Yellow, Faded}

(* ---------------------------------------------------------------------- *)
(* Index set of creatures *)
Creatures == 1 .. N

(* ---------------------------------------------------------------------- *)
(* Variables *)
VARIABLES creatures, mall, total

(* ---------------------------------------------------------------------- *)
(* Helper function: complement rule *)
Complement(col1, col2) ==
    IF col1 = col2
    THEN col1
    ELSE CHOOSE c \in {Blue, Red, Yellow} : c # col1 /\ c # col2

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ creatures \in [Creatures -> [color : {Blue, Red, Yellow}, meet : Nat]]
    /\ \A c \in Creatures :
          /\ creatures[c].color \in {Blue, Red, Yellow}
          /\ creatures[c].meet = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

(* ---------------------------------------------------------------------- *)
(* Action: a non‑faded creature enters an empty meeting place *)
Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
          /\ creatures[c].color # Faded
          /\ mall' = c
          /\ creatures' = creatures
          /\ total' = total

(* ---------------------------------------------------------------------- *)
(* Action: when the limit is reached a creature that tries to enter fades *)
Fade ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E c \in Creatures :
          /\ creatures[c].color # Faded
          /\ mall' = MeetingPlaceEmpty
          /\ creatures' = [creatures EXCEPT ![c] = [color |-> Faded,
                                                   meet  |-> @.meet]]
          /\ total' = total

(* ---------------------------------------------------------------------- *)
(* Action: two different creatures meet and mutate *)
Meet ==
    /\ mall \in Creatures               \* a creature is waiting
    /\ total < M
    /\ \E c2 \in Creatures :
          /\ c2 # mall
          /\ creatures[c2].color # Faded
          /\ LET c1 == mall IN
               LET newCol == Complement(creatures[c1].color,
                                         creatures[c2].color) IN
               /\ mall' = MeetingPlaceEmpty
               /\ total' = total + 1
               /\ creatures' = [creatures EXCEPT
                                   ![c1] = [color |-> newCol,
                                            meet  |-> @.meet + 1],
                                   ![c2] = [color |-> newCol,
                                            meet  |-> @.meet + 1]]
          /\ UNCHANGED << >>

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \/ Enter
    \/ Fade
    \/ Meet

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec ==
    Init /\ [][Next]_<<creatures, mall, total>>

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
    /\ creatures \in [Creatures -> [color : Colors, meet : Nat]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat

(* ---------------------------------------------------------------------- *)
(* Safety invariant: when the meeting limit is reached, the sum of individual
   meeting counts equals twice the limit. *)
SumMet ==
    total = M => 
        Sum({ creatures[c].meet : c \in Creatures }) = 2 * M

====