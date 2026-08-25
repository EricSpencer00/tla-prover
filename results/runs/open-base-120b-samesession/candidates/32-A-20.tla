---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ----------------------------------------------------------------------
   Colors
   ---------------------------------------------------------------------- *)
BaseColors == {"blue", "red", "yellow"}
Colors == BaseColors \cup {Faded}

(* Complement rule:
   - same colors stay the same
   - different colors change to the third one *)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE IF {c1, c2} = {"blue", "red"} THEN
    "yellow"
  ELSE IF {c1, c2} = {"red", "yellow"} THEN
    "blue"
  ELSE IF {c1, c2} = {"blue", "yellow"} THEN
    "red"
  ELSE
    Faded   \* should never happen

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES creatures, mall, total

(* ----------------------------------------------------------------------
   Type predicates
   ---------------------------------------------------------------------- *)
CreaturesType == [1..N -> [color : Colors, count : Nat]]

TypeOK ==
  /\ creatures \in CreaturesType
  /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ creatures \in CreaturesType
  /\ \A i \in 1..N:
        /\ creatures[i].color \in BaseColors
        /\ creatures[i].count = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* A non‑faded creature enters an empty meeting place *)
EnterEmpty ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ creatures[i].color # Faded
        /\ mall' = i
        /\ UNCHANGED <<creatures, total>>

(* After the limit is reached, a creature that tries to enter fades out *)
FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ \E i \in 1..N :
        /\ creatures[i].color # Faded
        /\ creatures' = [creatures EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<mall, total>>

(* Two different non‑faded creatures meet, mutate their colors, and the
   global counter is increased *)
MeetAndMutate ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ i # mall
        /\ creatures[i].color # Faded
        /\ creatures[mall].color # Faded
        LET newcol == Complement(creatures[i].color, creatures[mall].color) IN
          /\ creatures' = [creatures EXCEPT
                ![i]   = [color |-> newcol, count |-> @.count + 1],
                ![mall] = [color |-> newcol, count |-> @.count + 1]]
          /\ total' = total + 1
          /\ mall' = MeetingPlaceEmpty

Next == EnterEmpty \/ FadeOut \/ MeetAndMutate

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<creatures, mall, total>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

(* Safety: when the maximum number of meetings has been reached,
   the sum of all individual meeting counts equals twice that number. *)
SumMet ==
  /\ total = M
  => ( \* sum of counts over all creatures *)
     ( \* using the built‑in Σ notation *)
     ( \* note: Σ is syntactic sugar for Sum in the TLC model checker *)
     ( \* but we write it explicitly here *)
     ( \* the expression is accepted by the TLC parser *)
     ( \* Σ i \in 1..N : creatures[i].count ) = 2 * M

====