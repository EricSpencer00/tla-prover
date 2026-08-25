---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ---------------------------------------------------------------------- *)
(*  Colors                                                             *)
(* ---------------------------------------------------------------------- *)
Blue   == "Blue"
Red    == "Red"
Yellow == "Yellow"

Color == {Blue, Red, Yellow, Faded}

(* ---------------------------------------------------------------------- *)
(*  Complement rule                                                    *)
(* ---------------------------------------------------------------------- *)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE IF {c1, c2} = {Blue, Red}    THEN Yellow
  ELSE IF {c1, c2} = {Blue, Yellow} THEN Red
  ELSE IF {c1, c2} = {Red, Yellow}  THEN Blue
  ELSE Faded

(* ---------------------------------------------------------------------- *)
(*  State variables                                                    *)
(* ---------------------------------------------------------------------- *)
VARIABLES creatures, mall, total

vars == <<creatures, mall, total>>

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                      *)
(* ---------------------------------------------------------------------- *)
Init ==
  /\ creatures \in [1..N -> [color : {Blue, Red, Yellow}, met : Nat]]
  /\ \A i \in 1..N: creatures[i].met = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* ---------------------------------------------------------------------- *)
(*  Actions                                                            *)
(* ---------------------------------------------------------------------- *)

Enter(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ creatures[i].color # Faded
  /\ creatures' = creatures
  /\ total' = total
  /\ mall' = i

Fade(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ creatures[i].color # Faded
  /\ creatures' = [creatures EXCEPT ![i] = [color |-> Faded,
                                            met    |-> creatures[i].met]]
  /\ total' = total
  /\ mall' = MeetingPlaceEmpty

Meet(i, j) ==
  /\ mall = j
  /\ i # j
  /\ total < M
  /\ creatures[i].color # Faded
  /\ creatures[j].color # Faded
  /\ LET newcol == Complement(creatures[i].color, creatures[j].color) IN
        /\ creatures' = [creatures EXCEPT
                           ![i] = [color |-> newcol,
                                   met    |-> creatures[i].met + 1],
                           ![j] = [color |-> newcol,
                                   met    |-> creatures[j].met + 1]]
        /\ total' = total + 1
        /\ mall' = MeetingPlaceEmpty

EnterAction == ∃ i \in 1..N: Enter(i)
FadeAction  == ∃ i \in 1..N: Fade(i)
MeetAction  == ∃ i \in 1..N, j \in 1..N: Meet(i, j)

Next == EnterAction \/ FadeAction \/ MeetAction

(* ---------------------------------------------------------------------- *)
(*  Specification                                                      *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(*  Invariants                                                         *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
  /\ creatures \in [1..N -> [color : Color, met : Nat]]
  /\ mall \in {MeetingPlaceEmpty} \cup 1..N
  /\ total \in Nat
  /\ total <= M

TotalMetCounts == \Sum i \in 1..N: creatures[i].met

SumMet ==
  (total = M) => (TotalMetCounts = 2 * M)

(* ---------------------------------------------------------------------- *)
(*  The set of invariants required by the .cfg file                     *)
(* ---------------------------------------------------------------------- *)
INVARIANTS == TypeOK /\ SumMet

====