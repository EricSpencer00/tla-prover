---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ------------------------------------------------------------------- *)
(* Colors *)
Blue   == "blue"
Red    == "red"
Yellow == "yellow"

Colors      == {Blue, Red, Yellow}
AllColors   == Colors \cup {Faded}

(* ------------------------------------------------------------------- *)
(* State variables *)
VARIABLES state, mall, total

(* ------------------------------------------------------------------- *)
(* Complement rule *)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in Colors : c # c1 /\ c # c2

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ \E f \in [1..N -> Colors] :
        /\ state = [i \in 1..N |-> [color |-> f[i], meetCount |-> 0]]
        /\ mall  = MeetingPlaceEmpty
        /\ total = 0

(* ------------------------------------------------------------------- *)
(* Actions *)

Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ state' = state
        /\ mall'  = i
        /\ total' = total

Fade ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ mall'  = MeetingPlaceEmpty
        /\ total' = total

Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ i # mall
        /\ state[i].color # Faded
        /\ state[mall].color # Faded
        /\ LET newC == Complement(state[i].color, state[mall].color) IN
             /\ state' = [state EXCEPT
                           ![i].color      = newC,
                           ![i].meetCount  = @ + 1,
                           ![mall].color   = newC,
                           ![mall].meetCount = @ + 1]
             /\ mall'  = MeetingPlaceEmpty
             /\ total' = total + 1

Next == Enter \/ Fade \/ Meet

(* ------------------------------------------------------------------- *)
(* Specification *)
vars == <<state, mall, total>>
Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
  /\ state \in [1..N -> [color : AllColors, meetCount : Nat]]
  /\ mall  \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

SumMet ==
  (total = M) => (\Sum i \in 1..N : state[i].meetCount = 2 * M)

(* ------------------------------------------------------------------- *)

====