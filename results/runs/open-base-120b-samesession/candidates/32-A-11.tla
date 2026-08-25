---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* Colors *)
CONSTANTS Blue, Red, Yellow
Colors    == {Blue, Red, Yellow, Faded}
SubColors == {Blue, Red, Yellow}

(* Complement rule: if the two colors are equal keep it,
   otherwise return the third color from SubColors *)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE x \in SubColors \ {c1, c2} : TRUE

VARIABLES creatures, mall, total

vars == <<creatures, mall, total>>

(* ------------------------------------------------------------------------ *)
(* Type invariant *)
TypeOK ==
  /\ creatures \in [1..N -> [color : Colors, meetings : Nat]]
  /\ mall     \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total    \in Nat
  /\ total <= M

(* ------------------------------------------------------------------------ *)
(* Initial state *)
Init ==
  /\ creatures \in [1..N -> [color : SubColors, meetings : Nat]]
  /\ \A c \in 1..N : creatures[c].meetings = 0
  /\ mall   = MeetingPlaceEmpty
  /\ total  = 0

(* ------------------------------------------------------------------------ *)
(* Actions *)

Enter ==
  \E c \in 1..N :
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ creatures[c].color # Faded
    /\ mall' = c
    /\ creatures' = creatures
    /\ total' = total

FadeOut ==
  \E c \in 1..N :
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ creatures[c].color # Faded
    /\ creatures' = [creatures EXCEPT ![c] = [color |-> Faded,
                                             meetings |-> @.meetings]]
    /\ mall' = MeetingPlaceEmpty
    /\ total' = total

Meet ==
  \E c \in 1..N :
    /\ mall # MeetingPlaceEmpty
    /\ c # mall
    /\ total < M
    /\ creatures[c].color # Faded
    /\ creatures[mall].color # Faded
    /\ LET w      == mall
           newCol == Complement(creatures[w].color, creatures[c].color)
       IN
          /\ creatures' = [creatures EXCEPT
                ![w] = [color |-> newCol,
                        meetings |-> @.meetings + 1],
                ![c] = [color |-> newCol,
                        meetings |-> @.meetings + 1]]
          /\ mall'   = MeetingPlaceEmpty
          /\ total'  = total + 1

Next == \/ Enter \/ FadeOut \/ Meet

(* ------------------------------------------------------------------------ *)
(* Specification *)
Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------ *)
(* Safety invariant about meeting counts *)
SumMet ==
  (total = M) => (∑ c \in 1..N : creatures[c].meetings) = 2 * M

====