---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* derived sets *)
Creatures == 1..N
BaseColors == {Blue, Red, Yellow}
Colors == BaseColors \cup {Faded}

VARIABLES state, place, total

(* complement rule *)
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE col \in BaseColors : col # c1 /\ col # c2

(* initial state *)
Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in BaseColors : TRUE,
                                    count |-> 0]]
    /\ place = MeetingPlaceEmpty
    /\ total = 0

(* actions *)

Enter ==
    /\ place = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
        /\ state[c].color # Faded
        /\ place' = c
        /\ UNCHANGED <<state, total>>

Fade ==
    /\ place = MeetingPlaceEmpty
    /\ total = M
    /\ \E c \in Creatures :
        /\ state[c].color # Faded
        /\ state' = [state EXCEPT ![c].color = Faded]
        /\ UNCHANGED <<place, total>>

Meet ==
    /\ place # MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
        /\ c # place
        /\ state[c].color # Faded
        /\ state[place].color # Faded
        /\ LET newColor == Complement(state[c].color, state[place].color) IN
            /\ state' = [state EXCEPT
                           ![c].color = newColor,
                           ![c].count = @ + 1,
                           ![place].color = newColor,
                           ![place].count = @ + 1]
            /\ total' = total + 1
            /\ place' = MeetingPlaceEmpty

Next == Enter \/ Fade \/ Meet

(* type invariant *)
TypeOK ==
    /\ state \in [Creatures -> [color : Colors, count : Nat]]
    /\ place \in (Creatures \cup {MeetingPlaceEmpty})
    /\ total \in Nat
    /\ total <= M

(* safety invariant *)
SumMet ==
    (total = M) => ((∑ c \in Creatures : state[c].count) = 2 * M)

vars == <<state, place, total>>
Spec == Init /\ [][Next]_vars

====