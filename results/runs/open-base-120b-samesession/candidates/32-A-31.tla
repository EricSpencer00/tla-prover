---- MODULE Chameneos ----
EXTENDS Naturals, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ----------------------------------------------------------------------
   Colors
   ---------------------------------------------------------------------- *)
Color == {"blue", "red", "yellow", Faded}
BaseColors == {"blue", "red", "yellow"}

(* ----------------------------------------------------------------------
   Complement rule
   ---------------------------------------------------------------------- *)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in BaseColors :
        /\ c # c1
        /\ c # c2

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES creatures, mall, total

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ creatures \in [1..N -> (Color \X Nat)]
  /\ mall \in {MeetingPlaceEmpty} \cup 1..N
  /\ total \in Nat

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ creatures = [i \in 1..N |-> << CHOOSE col \in BaseColors : TRUE, 0 >>]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* A non‑faded creature enters an empty meeting place *)
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in 1..N :
        /\ creatures[c][1] # Faded
        /\ mall' = c
        /\ creatures' = creatures
        /\ total' = total

(* After the limit is reached, a creature that tries to enter fades out *)
Fade ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ \E c \in 1..N :
        /\ creatures[c][1] # Faded
        /\ creatures' = [creatures EXCEPT ![c][1] = Faded]
        /\ mall' = MeetingPlaceEmpty
        /\ total' = total

(* Two different creatures meet and mutate their colors *)
Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E a \in 1..N :
        /\ a # mall
        /\ creatures[a][1] # Faded
        /\ LET p      == mall
               colP   == creatures[p][1]
               colA   == creatures[a][1]
               newCol == Complement(colP, colA)
           IN
               /\ creatures' = [creatures EXCEPT
                                   ![p][1] = newCol,
                                   ![p][2] = @ + 1,
                                   ![a][1] = newCol,
                                   ![a][2] = @ + 1]
               /\ mall' = MeetingPlaceEmpty
               /\ total' = total + 1

Next == Enter \/ Fade \/ Meet

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<creatures, mall, total>>

(* ----------------------------------------------------------------------
   Safety invariant about the sum of meeting counts
   ---------------------------------------------------------------------- *)
SumMet ==
  (total = M) => (\Sum i \in 1..N : creatures[i][2] = 2 * M)

====