---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ---------------------------------------------------------------------- *)
(* Colors *)
Blue == "Blue"
Red  == "Red"
Yellow == "Yellow"

ColorSet == {Blue, Red, Yellow, Faded}
NonFadedColors == {Blue, Red, Yellow}

(* ---------------------------------------------------------------------- *)
(* State variables *)
VARIABLES creature, mall, total

(* creature[i] = [color |-> c, cnt |-> n] for creature i *)
(* mall = MeetingPlaceEmpty or a creature identifier in 1..N *)
(* total = total number of completed meetings *)

(* ---------------------------------------------------------------------- *)
(* Complement rule *)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in NonFadedColors : c # c1 /\ c # c2

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ creature \in [1..N -> [color : ColorSet, cnt : Nat]]
  /\ \A i \in 1..N :
        /\ creature[i].color \in NonFadedColors
        /\ creature[i].cnt = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* ---------------------------------------------------------------------- *)
(* Actions *)

Enter(id) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ id \in 1..N
  /\ creature[id].color # Faded
  /\ mall' = id
  /\ UNCHANGED <<creature, total>>

Fade(id) ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ id \in 1..N
  /\ creature[id].color # Faded
  /\ creature' = [creature EXCEPT ![id].color = Faded]
  /\ UNCHANGED <<mall, total>>

Meet(id) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall \in 1..N
  /\ id \in 1..N
  /\ id # mall
  /\ total < M
  /\ creature[id].color # Faded
  /\ creature[mall].color # Faded
  /\ let newColor == Complement(creature[id].color, creature[mall].color) in
        creature' = [creature EXCEPT
                       ![id].color = newColor,
                       ![id].cnt   = @ + 1,
                       ![mall].color = newColor,
                       ![mall].cnt   = @ + 1]
  /\ mall' = MeetingPlaceEmpty
  /\ total' = total + 1

Next ==
  \E id \in 1..N :
    \/ Enter(id)
    \/ Fade(id)
    \/ Meet(id)

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec ==
  Init /\ [][Next]_<<creature, mall, total>>

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
  /\ creature \in [1..N -> [color : ColorSet, cnt : Nat]]
  /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat

(* ---------------------------------------------------------------------- *)
(* Safety invariant: sum of individual meeting counts equals 2*M when total = M *)
SumMet ==
  (total = M) => (Sum(i \in 1..N, creature[i].cnt) = 2 * M)

====