---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty
ASSUME /\ N \in Nat /\ N > 0
       /\ M \in Nat /\ M > 0
       /\ Faded \notin {"blue", "red", "yellow"}

\* Colors live in a small fixed set; meeting elsewhere uses the complement
\* rule given in the problem statement (different => third color, same => same).
Colors == {"blue", "red", "yellow"}
\* The third color, indexed so the rule can be expressed with arithmetic.
Third == [a \in Colors |-> [b \in Colors |->
    IF a = b THEN a ELSE IF (a = "blue" /\ b = "red") \/ (a = "red" /\ b = "blue") THEN "yellow"
    ELSE IF (a = "blue" /\ b = "yellow") \/ (a = "yellow" /\ b = "blue") THEN "red"
    ELSE "blue"]]

\* A creature is a record with a color (or Faded) and a personal meeting count.
Creatures == [color : Colors \cup {Faded}, met : 0..M]

VARIABLES atPlace, occupant, standing
vars == <<atPlace, occupant, standing>>

RECURSIVE TotalMet(_)
TotalMet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN standing[x].met + TotalMet(S \ {x})

TypeOK ==
    /\ atPlace \in [Creatures -> BOOLEAN]
    /\ occupant \in Creatures \cup {MeetingPlaceEmpty}
    /\ standing \in [Creatures -> Creatures]

Init ==
    /\ atPlace = [c \in Creatures |-> TRUE]
    /\ \E initcol \in [Creatures -> Colors] :
        standing = [c \in Creatures |-> [color |-> initcol[c], met |-> 0]]
    /\ occupant = MeetingPlaceEmpty

Enter(c) ==
    /\ atPlace[c]
    /\ occupant = MeetingPlaceEmpty
    /\ standing[c].color # Faded
    /\ standing[c].met < M
    /\ occupant' = c
    /\ UNCHANGED <<atPlace, standing>>

Fade(c) ==
    /\ atPlace[c]
    /\ occupant = MeetingPlaceEmpty
    /\ (standing[c].met = M \/ \A x \in Creatures : standing[x].met = M)
    /\ standing[c].color # Faded
    /\ standing' = [standing EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<atPlace, occupant>>

MeetAndMutate(c) ==
    /\ occupant # MeetingPlaceEmpty
    /\ occupant # c
    /\ atPlace[c]
    /\ standing[c].color # Faded
    /\ standing[occupant].color # Faded
    /\ standing[c].met < M
    /\ standing[occupant].met < M
    /\ atPlace' = [atPlace EXCEPT ![c] = FALSE]
    /\ standing' = [standing EXCEPT ![c] = [color |-> Third[standing[c].color][standing[occupant].color],
                                          met |-> @.met + 1],
                                 ![occupant] = [color |-> Third[standing[c].color][standing[occupant].color],
                                                met |-> @.met + 1]]
    /\ occupant' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : Fade(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* Safety: the global counter is implicit as the sum of all per-creature values,
\* so the bounded meeting budget is reflected at both levels together.
SumMet == TotalMet(Creatures) = 2 * M
====