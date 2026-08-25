---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ------------------------------------------------------------------- *)
(* Colors *)
Blue   == "blue"
Red    == "red"
Yellow == "yellow"

BaseColors == {Blue, Red, Yellow}
Colors     == BaseColors \cup {Faded}

(* ------------------------------------------------------------------- *)
(* State variables *)
VARIABLES creatures, place, total

(* ------------------------------------------------------------------- *)
(* Complement rule *)
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in BaseColors : c # c1 /\ c # c2

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ creatures = [i \in 1..N |-> [color |-> CHOOSE c \in BaseColors : TRUE,
                                   count |-> 0]]
    /\ place = MeetingPlaceEmpty
    /\ total = 0

(* ------------------------------------------------------------------- *)
(* Actions *)

(* A non‑faded creature enters an empty meeting place *)
Enter ==
    /\ place = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
          /\ creatures[i].color # Faded
          /\ place' = i
          /\ UNCHANGED <<creatures, total>>

(* When the limit is reached, a creature that tries to enter fades out *)
FadeOut ==
    /\ place = MeetingPlaceEmpty
    /\ total >= M
    /\ \E i \in 1..N :
          /\ creatures[i].color # Faded
          /\ creatures' = [creatures EXCEPT ![i].color = Faded]
          /\ UNCHANGED <<place, total>>

(* Two different creatures meet and both mutate their colors *)
Meet ==
    /\ place # MeetingPlaceEmpty               \* there is a waiting creature
    /\ total < M
    /\ \E i \in 1..N :
          /\ i # place
          /\ creatures[i].color # Faded
          /\ LET j == place IN
                newColor == Complement(creatures[i].color, creatures[j].color) IN
                /\ creatures' = [creatures EXCEPT
                                   ![i] = [color |-> newColor,
                                           count |-> creatures[i].count + 1],
                                   ![j] = [color |-> newColor,
                                           count |-> creatures[j].count + 1]]
                /\ total' = total + 1
                /\ place' = MeetingPlaceEmpty

Next == Enter \/ FadeOut \/ Meet

(* ------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<creatures, place, total>>

(* ------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ creatures \in [1..N -> [color : Colors, count : Nat]]
    /\ place \in {MeetingPlaceEmpty} \cup 1..N
    /\ total \in Nat
    /\ total <= M
    /\ IF place # MeetingPlaceEmpty THEN creatures[place].color # Faded ELSE TRUE

SumMet ==
    (total = M) => (Sum({i \in 1..N : creatures[i].count}) = 2 * M)

====