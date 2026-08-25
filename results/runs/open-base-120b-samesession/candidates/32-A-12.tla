---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty
CONSTANTS Blue, Red, Yellow

(* ------------------------------------------------------------------------ *)
(* Sets and derived constants *)
Colors          == {Blue, Red, Yellow, Faded}
NonFadedColors == {Blue, Red, Yellow}
CreatureIds     == 1..N

(* ------------------------------------------------------------------------ *)
(* Variables *)
VARIABLES state, mp, total

(* ------------------------------------------------------------------------ *)
(* Initial state *)
Init ==
    /\ state = [i \in CreatureIds |-> 
                   [ color |-> CHOOSE c \in NonFadedColors : TRUE,
                     count |-> 0 ]]
    /\ mp    = MeetingPlaceEmpty
    /\ total = 0

(* ------------------------------------------------------------------------ *)
(* Complement rule *)
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in NonFadedColors : c # c1 /\ c # c2

(* ------------------------------------------------------------------------ *)
(* Actions *)

EnterEmpty ==
    \E i \in CreatureIds :
        /\ state[i].color # Faded
        /\ mp = MeetingPlaceEmpty
        /\ total < M
        /\ mp' = i
        /\ UNCHANGED <<state, total>>

FadeOut ==
    \E i \in CreatureIds :
        /\ state[i].color # Faded
        /\ mp = MeetingPlaceEmpty
        /\ total = M
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<mp, total>>

MeetAndMutate ==
    \E i, j \in CreatureIds :
        /\ i # j
        /\ mp = j
        /\ total < M
        /\ state[i].color # Faded
        /\ state[j].color # Faded
        LET newc == Complement(state[i].color, state[j].color) IN
            /\ state' = [state EXCEPT 
                           ![i].color = newc,
                           ![i].count = @ + 1,
                           ![j].color = newc,
                           ![j].count = @ + 1]
            /\ total' = total + 1
            /\ mp'    = MeetingPlaceEmpty

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

(* ------------------------------------------------------------------------ *)
(* Specification *)
Spec ==
    Init /\ [][Next]_<<state, mp, total>>

(* ------------------------------------------------------------------------ *)
(* Invariants *)

TypeOK ==
    /\ state \in [CreatureIds -> [color: Colors, count: Nat]]
    /\ mp    \in (CreatureIds \cup {MeetingPlaceEmpty})
    /\ total \in Nat

SumMet ==
    (total = M) => (Sum(i \in CreatureIds: state[i].count) = 2 * M)

====