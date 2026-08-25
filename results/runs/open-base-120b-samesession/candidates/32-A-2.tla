---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*-------------------------------------------------------------------*)
(* Set of creature identifiers                                         *)
CREATURE == 1..N

(*-------------------------------------------------------------------*)
(* Complement rule for colors                                          *)
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in {"blue", "red", "yellow"} :
            /\ c # c1
            /\ c # c2

(*-------------------------------------------------------------------*)
(* Variables                                                          *)
VARIABLES col, cnt, mall, total

(*-------------------------------------------------------------------*)
(* Initial state                                                       *)
Init ==
    /\ col \in [CREATURE -> {"blue", "red", "yellow"}]      \* nondet initial colors
    /\ cnt = [i \in CREATURE |-> 0]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

(*-------------------------------------------------------------------*)
(* Action: a creature enters an empty meeting place                     *)
Enter(i) ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ col[i] # Faded
    /\ mall' = i
    /\ UNCHANGED << col, cnt, total >>

(*-------------------------------------------------------------------*)
(* Action: a creature fades out when the limit is reached               *)
Fade(i) ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ col[i] # Faded
    /\ col' = [col EXCEPT ![i] = Faded]
    /\ UNCHANGED << cnt, mall, total >>

(*-------------------------------------------------------------------*)
(* Action: two different creatures meet and mutate colors               *)
Meet(i) ==
    LET j == mall IN
    /\ j # MeetingPlaceEmpty
    /\ i # j
    /\ col[i] # Faded
    /\ col[j] # Faded
    /\ total < M
    LET newColor == Complement(col[i], col[j]) IN
        /\ col' = [col EXCEPT ![i] = newColor, ![j] = newColor]
        /\ cnt' = [cnt EXCEPT ![i] = cnt[i] + 1, ![j] = cnt[j] + 1]
        /\ total' = total + 1
        /\ mall' = MeetingPlaceEmpty

(*-------------------------------------------------------------------*)
(* Next-state relation                                                  *)
Next ==
    \/ \E i \in CREATURE : Enter(i)
    \/ \E i \in CREATURE : Fade(i)
    \/ \E i \in CREATURE : Meet(i)

(*-------------------------------------------------------------------*)
(* Variables tuple for stuttering                                         *)
vars == << col, cnt, mall, total >>

(*-------------------------------------------------------------------*)
(* Specification                                                       *)
Spec == Init /\ [][Next]_vars

(*-------------------------------------------------------------------*)
(* Type invariants                                                     *)
TypeOK ==
    /\ col \in [CREATURE -> {"blue", "red", "yellow", Faded}]
    /\ cnt \in [CREATURE -> Nat]
    /\ mall \in CREATURE \cup {MeetingPlaceEmpty}
    /\ total \in Nat

(*-------------------------------------------------------------------*)
(* Safety property: sum of individual meeting counts equals twice the *)
(* number of global meetings when the limit is reached.                *)
SumMet ==
    total = M => Sum(i \in CREATURE, cnt[i]) = 2 * M

====