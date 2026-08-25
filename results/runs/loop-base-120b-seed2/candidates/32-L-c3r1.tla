---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ---------------------------------------------------------------------- *)
(* Colors *)
Blue   == "blue"
Red    == "red"
Yellow == "yellow"

ColorSet == {Blue, Red, Yellow, Faded}
BaseColors == {Blue, Red, Yellow}

(* ---------------------------------------------------------------------- *)
(* Complement rule *)
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in BaseColors : c # c1 /\ c # c2

(* ---------------------------------------------------------------------- *)
(* State variables *)
VARIABLES cr, place, total

(* ---------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
    /\ cr \in [i \in 1..N |-> [color : ColorSet, count : Nat]]
    /\ place \in ({MeetingPlaceEmpty} \cup 1..N)
    /\ total \in Nat

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ cr \in [i \in 1..N |-> [color : BaseColors, count : Nat]]
    /\ \A i \in 1..N : cr[i].count = 0
    /\ place = MeetingPlaceEmpty
    /\ total = 0

(* ---------------------------------------------------------------------- *)
(* Actions *)

(* A non‑faded creature enters an empty meeting place while the system is still open *)
EnterEmpty ==
    /\ place = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
          /\ cr[i].color # Faded
          /\ place' = i
          /\ UNCHANGED << cr, total >>

(* After the limit is reached, a creature that tries to enter fades out *)
FadeOut ==
    /\ place = MeetingPlaceEmpty
    /\ total >= M
    /\ \E i \in 1..N :
          /\ cr[i].color # Faded
          /\ cr' = [cr EXCEPT ![i].color = Faded]
          /\ UNCHANGED << place, total >>

(* Two different non‑faded creatures meet, change color, and update counters *)
MeetAndMutate ==
    /\ place # MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
          /\ i # place
          /\ cr[i].color # Faded
          /\ cr[place].color # Faded
          /\ LET newColor == Complement(cr[i].color, cr[place].color) IN
                /\ cr' = [cr EXCEPT
                           ![i].color    = newColor,
                           ![i].count    = @ + 1,
                           ![place].color = newColor,
                           ![place].count = @ + 1]
                /\ total' = total + 1
                /\ place' = MeetingPlaceEmpty

(* ---------------------------------------------------------------------- *)
Next == \/ EnterEmpty
        \/ FadeOut
        \/ MeetAndMutate

(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<cr, place, total>>

(* ---------------------------------------------------------------------- *)
(* Safety property: when the global counter reaches the limit, the sum of
   individual meeting counts equals twice that limit *)
SumMet ==
    (total = M) => (∑ i \in 1..N : cr[i].count) = 2 * M

====