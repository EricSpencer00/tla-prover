---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty
CONSTANTS Blue, Red, Yellow

(* ----------------------------------------------------------------------
   Sets and helper definitions
   ---------------------------------------------------------------------- *)
ColorSet          == {Blue, Red, Yellow, Faded}
NonFadedColors    == {Blue, Red, Yellow}
CreatureSet       == 1..N

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in NonFadedColors : c # c1 /\ c # c2

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES creature, mall, total

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ total \in Nat
    /\ mall \in CreatureSet \cup {MeetingPlaceEmpty}
    /\ creature \in [CreatureSet -> [color : ColorSet, cnt : Nat]]
    /\ \A i \in CreatureSet :
          creature[i].color = Faded => creature[i].cnt \in Nat

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ total = 0
    /\ mall  = MeetingPlaceEmpty
    /\ \A i \in CreatureSet :
          creature[i] = [color |-> CHOOSE c \in NonFadedColors : TRUE,
                         cnt   |-> 0]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* A non‑faded creature enters an empty meeting place while meetings are still allowed *)
EnterEmpty ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in CreatureSet :
          /\ creature[i].color # Faded
          /\ mall' = i
          /\ UNCHANGED <<creature, total>>

(* The meeting place is closed; a creature that attempts to enter fades out *)
FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E i \in CreatureSet :
          /\ creature[i].color # Faded
          /\ creature' = [creature EXCEPT ![i].color = Faded]
          /\ UNCHANGED <<mall, total>>

(* Two different non‑faded creatures meet, change color, and update counters *)
MeetAndMutate ==
    /\ mall # MeetingPlaceEmpty               \* there is a waiting creature
    /\ total < M
    /\ \E i \in CreatureSet :
          /\ i # mall
          /\ creature[i].color # Faded
          /\ creature[mall].color # Faded
          /\ LET newColor == Complement(creature[i].color,
                                        creature[mall].color) IN
                /\ creature' = [creature EXCEPT
                                   ![i].color = newColor,
                                   ![i].cnt   = creature[i].cnt + 1,
                                   ![mall].color = newColor,
                                   ![mall].cnt   = creature[mall].cnt + 1]
                /\ total' = total + 1
                /\ mall'  = MeetingPlaceEmpty

Next == \/ EnterEmpty \/ FadeOut \/ MeetAndMutate

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<creature, mall, total>>

(* ----------------------------------------------------------------------
   Safety invariant
   ---------------------------------------------------------------------- *)
SumMet ==
    total = M => Sum({ creature[i].cnt : i \in CreatureSet }) = 2 * M

====