---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* --------------------------------------------------------------------- *)
(*   Definitions of colors                                              *)
(* --------------------------------------------------------------------- *)

ColorsNoFaded == {"blue", "red", "yellow"}
Colors == ColorsNoFaded \cup {Faded}

(* Complement rule: if colors are equal keep them, otherwise the third one *)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in ColorsNoFaded : c # c1 /\ c # c2

(* --------------------------------------------------------------------- *)
(*   State variables                                                    *)
(* --------------------------------------------------------------------- *)

VARIABLES creatures, mall, total

(* creatures : [1..N -> [color : Colors, count : Nat]]                *)

(* --------------------------------------------------------------------- *)
(*   Initial state                                                      *)
(* --------------------------------------------------------------------- *)

Init ==
  /\ creatures = [i \in 1..N |-> [color |-> CHOOSE c \in ColorsNoFaded : TRUE,
                                 count |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* --------------------------------------------------------------------- *)
(*   Actions                                                            *)
(* --------------------------------------------------------------------- *)

Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
       /\ creatures[i].color # Faded
       /\ mall' = i
       /\ UNCHANGED <<creatures, total>>

Fade ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ \E i \in 1..N :
       /\ creatures[i].color # Faded
       /\ creatures' = [creatures EXCEPT ![i].color = Faded]
       /\ UNCHANGED <<mall, total>>

Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
       /\ i # mall
       /\ creatures[i].color # Faded
       /\ creatures[mall].color # Faded
       /\ LET newCol == Complement(creatures[i].color,
                                   creatures[mall].color) IN
            /\ creatures' =
                 [j \in 1..N |-> IF j = i \/ j = mall
                                THEN [color |-> newCol,
                                      count |-> creatures[j].count + 1]
                                ELSE creatures[j]]
            /\ total' = total + 1
            /\ mall' = MeetingPlaceEmpty

Next ==
  \/ Enter
  \/ Fade
  \/ Meet

(* --------------------------------------------------------------------- *)
(*   Specification                                                      *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<creatures, mall, total>>

(* --------------------------------------------------------------------- *)
(*   Invariants                                                         *)
(* --------------------------------------------------------------------- *)

TypeOK ==
  /\ creatures \in [1..N -> [color : Colors, count : Nat]]
  /\ mall \in (MeetingPlaceEmpty \cup 1..N)
  /\ total \in Nat
  /\ total <= M

SumMet ==
  (total = M) => (Sum({creatures[i].count : i \in 1..N}) = 2 * M)

=============================================================================