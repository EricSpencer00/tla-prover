---- MODULE Chameneos ----
EXTENDS Naturals, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ------------------------------------------------------------------------- *)
(*   Color definitions                                                       *)
(* ------------------------------------------------------------------------- *)

Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}
ThirdColor(c1, c2) == 
  IF c1 = c2 THEN c1 
  ELSE CHOOSE c \in NonFadedColors : c # c1 /\ c # c2

(* ------------------------------------------------------------------------- *)
(*   State variables                                                        *)
(* ------------------------------------------------------------------------- *)

VARIABLES state, waiting, total

(* state : [1..N -> [color : Colors, count : Nat]] *)
(* waiting : either MeetingPlaceEmpty or a creature id in 1..N               *)
(* total : Nat, number of meetings that have occurred                         *)

(* ------------------------------------------------------------------------- *)
(*   Initial state                                                          *)
(* ------------------------------------------------------------------------- *)

Init ==
  /\ state = [i \in 1..N |-> [color |-> CHOOSE c \in NonFadedColors : TRUE,
                             count |-> 0]]
  /\ waiting = MeetingPlaceEmpty
  /\ total = 0

(* ------------------------------------------------------------------------- *)
(*   Actions                                                                *)
(* ------------------------------------------------------------------------- *)

EnterEmptyPlace(i) ==
  /\ i \in 1..N
  /\ state[i].color # Faded
  /\ waiting = MeetingPlaceEmpty
  /\ total < M
  /\ waiting' = i
  /\ UNCHANGED << state, total >>

FadeOut(i) ==
  /\ i \in 1..N
  /\ state[i].color # Faded
  /\ waiting = MeetingPlaceEmpty
  /\ total >= M
  /\ state' = [state EXCEPT ![i].color = Faded]
  /\ waiting' = MeetingPlaceEmpty
  /\ UNCHANGED total

MeetAndMutate(i) ==
  /\ i \in 1..N
  /\ state[i].color # Faded
  /\ waiting # MeetingPlaceEmpty
  /\ waiting # i
  /\ LET j == waiting IN
        /\ LET newCol == ThirdColor(state[i].color, state[j].color) IN
           /\ state' = [state EXCEPT 
                         ![i].color = newCol,
                         ![i].count = @ + 1,
                         ![j].color = newCol,
                         ![j].count = @ + 1]
  /\ total' = total + 1
  /\ waiting' = MeetingPlaceEmpty

Next ==
  \/ \E i \in 1..N: EnterEmptyPlace(i)
  \/ \E i \in 1..N: FadeOut(i)
  \/ \E i \in 1..N: MeetAndMutate(i)
  \/ /\ waiting = MeetingPlaceEmpty
     /\ total >= M
     /\ UNCHANGED << state, waiting, total >>

(* ------------------------------------------------------------------------- *)
(*   Specification                                                          *)
(* ------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<state, waiting, total>>

(* ------------------------------------------------------------------------- *)
(*   Safety invariant                                                       *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
  /\ state \in [1..N -> [color : Colors, count : Nat]]
  /\ waiting \in {MeetingPlaceEmpty} \cup 1..N
  /\ total \in Nat

SumMet ==
  (total = M) => 
    ( /\ (\A i \in 1..N : state[i].count >= 0)
      /\ ( \A i \in 1..N : state[i].color # Faded => state[i].count >= 0 )
      /\ ( \A i \in 1..N : state[i].color = Faded => state[i].count >= 0 )
      /\ ( \A i \in 1..N : state[i].color = Faded => state[i].color # Faded ) 
      /\ ( \A i \in 1..N : state[i].color # Faded => state[i].color \in NonFadedColors )
      /\ ( \A i \in 1..N : state[i].color \in Colors )
      /\ ( \A i \in 1..N : state[i].count \in Nat )
      /\ ( \A i \in 1..N : state[i].count >= 0 )
      /\ ( \A i \in 1..N : state[i].count \in Nat )
      /\ ( \Sum i \in 1..N : state[i].count = 2 * M )
    )

(*
  The additional conjuncts inside SumMet are redundant but help TLC
  to keep the invariant simple and type‑safe. The essential safety claim
  is that when the global counter reaches the limit M, the sum of all
  individual meeting counts equals exactly twice M.
*)

=============================================================================