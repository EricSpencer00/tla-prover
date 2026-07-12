---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Ingredients, Offers

(* --- VARIABLES --- *)
VARIABLES smoker, offer

(* Type definitions *)
\* smokes[ingredient] is true iff the smoker who owns `ingredient`
\* is currently smoking
TypeOK == smokes \in [Ingredients -> BOOLEAN] /\ offer \in Ingredients \cup {""}

(* --- INITIAL STATE --- *)
Init ==
  /\ smokes = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

(* --- ACTIONS --- *)

StartSmoking ==
  /\ offer # ""                         \* there is a current offer
  /\ \E i \in Ingredients :
        /\ smokes[i] = FALSE           \* only non-smoking smokers can start
        /\ (offer \cup {i}) = Ingredients   \* offer plus the smoker's ingredient makes full set
        /\ smokes' = [smokes EXCEPT ![i] = TRUE]
        /\ offer' = ""

StopSmoking ==
  /\ offer = ""                         \* current smoker is on the table
  /\ \E i \in Ingredients :
        /\ smokes[i] = TRUE
        /\ smokes' = [smokes EXCEPT ![i] = FALSE]
        /\ offer' \in Offers

NEXT ==
  StartSmoking \/ StopSmoking

(* --- INVARIANT: AT MOST ONE SMOKER -- *)
AtMostOne == Cardinality({i \in Ingredients: smokes[i]}) <= 1

(* --- FULL SPECIFICATION --- *)
Spec == Init /\ [][NEXT]_<<smokes, offer>>

====