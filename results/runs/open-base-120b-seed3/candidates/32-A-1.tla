---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* --------------------------------------------------------------------- *)
(* Color definitions *)
ColorsNoFaded == {"blue", "red", "yellow"}
Color == ColorsNoFaded \cup {Faded}

(* --------------------------------------------------------------------- *)
(* State variables *)
VARIABLES C, mall, total

(* --------------------------------------------------------------------- *)
(* Complement rule *)
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in ColorsNoFaded : c # c1 /\ c # c2

(* --------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ C = [i \in 1..N |-> [color |-> CHOOSE c \in ColorsNoFaded : TRUE,
                            count |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

(* --------------------------------------------------------------------- *)
(* Actions *)

Enter(i) ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ C[i].color # Faded
    /\ mall' = i
    /\ UNCHANGED <<C, total>>

Fade(i) ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ C[i].color # Faded
    /\ C' = [C EXCEPT ![i].color = Faded]
    /\ UNCHANGED <<mall, total>>

Meet(i) ==
    /\ mall # MeetingPlaceEmpty
    /\ LET j == mall IN
         /\ i # j
         /\ total < M
         /\ C[i].color # Faded
         /\ C[j].color # Faded
         /\ LET newCol == Complement(C[i].color, C[j].color) IN
              /\ C' = [C EXCEPT ![i].color = newCol,
                               ![i].count = @+1,
                               ![j].color = newCol,
                               ![j].count = @+1]
              /\ total' = total + 1
              /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Fade(i)
    \/ \E i \in 1..N : Meet(i)

(* --------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<C, mall, total>>

(* --------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ C \in [1..N -> [color: Color, count: Nat]]
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat

SumMet ==
    IF total = M
    THEN  Sum({i \in 1..N : C[i].count}) = 2 * M
    ELSE TRUE

====