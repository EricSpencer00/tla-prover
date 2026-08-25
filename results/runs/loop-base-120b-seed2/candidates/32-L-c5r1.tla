---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ---------------------------------------------------------------------- *)
(* Colors *)
ColorSet == {"blue", "red", "yellow", Faded}

(* ---------------------------------------------------------------------- *)
(* State variables *)
VARIABLES creatures, place, total

(* ---------------------------------------------------------------------- *)
(* Helper accessors *)
Color(c) == creatures[c].color
Count(c) == creatures[c].count

(* ---------------------------------------------------------------------- *)
(* Complement rule *)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    CASE
      (c1 = "blue" /\ c2 = "red") \/ (c1 = "red" /\ c2 = "blue") -> "yellow" []
      (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") -> "red" []
      (c1 = "red" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "red") -> "blue"
    END

(* ---------------------------------------------------------------------- *)
(* Initialization *)
Init ==
  /\ creatures = [i \in 1..N |-> 
        [ color |-> CHOOSE col \in {"blue","red","yellow"} : TRUE,
          count |-> 0 ]]
  /\ place = MeetingPlaceEmpty
  /\ total = 0

(* ---------------------------------------------------------------------- *)
(* Actions *)

Enter ==
  /\ place = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in 1..N :
        /\ Color(c) # Faded
        /\ UNCHANGED creatures
        /\ place' = c
        /\ total' = total

Fade ==
  /\ place = MeetingPlaceEmpty
  /\ total = M
  /\ \E c \in 1..N :
        /\ Color(c) # Faded
        /\ creatures' = [creatures EXCEPT ![c].color = Faded]
        /\ UNCHANGED <<place, total>>

Meet ==
  /\ total < M
  /\ \E c1 \in 1..N :
        /\ place = c1
        /\ \E c2 \in 1..N :
            /\ c2 # c1
            /\ Color(c1) # Faded
            /\ Color(c2) # Faded
            /\ LET newColor == Complement(Color(c1), Color(c2)) IN
               /\ creatures' = [creatures EXCEPT
                                 ![c1] = [color |-> newColor, count |-> Count(c1) + 1],
                                 ![c2] = [color |-> newColor, count |-> Count(c2) + 1]]
               /\ place' = MeetingPlaceEmpty
               /\ total' = total + 1

Next ==
  \/ Enter
  \/ Fade
  \/ Meet

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec ==
  Init /\ [][Next]_<<creatures, place, total>>

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
  /\ creatures \in [1..N -> [color : ColorSet, count : Nat]]
  /\ place \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

SumMet ==
  /\ total = M
  => ( /\ Sum({i \in 1..N : creatures[i].count}) = 2 * M)

====