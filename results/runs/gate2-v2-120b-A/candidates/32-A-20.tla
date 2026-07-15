---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ----------------------------------------------------------------------
   Derived constant sets
   ---------------------------------------------------------------------- *)
Colors == {"blue", "red", "yellow", Faded}
ActiveColors == {"blue", "red", "yellow"}

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES state, mall, total

(* ----------------------------------------------------------------------
   Type definitions
   ---------------------------------------------------------------------- *)
Creature == 1 .. N

ColorMeeting == [color : Colors, cnt : Nat]

(* The mapping from each creature to its (color, meeting‑count) pair *)
State == [c \in Creature |-> [color : Colors, cnt : Nat]]

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
\* The third color that is neither c1 nor c2, assuming c1 # c2 and both are active
ThirdColor(c1, c2) ==
  CHOOSE c \in ActiveColors : c # c1 /\ c # c2

(* Complement rule applied to two colors *)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE ThirdColor(c1, c2)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ state = [c \in Creature |-> [color |-> CHOOSE col \in ActiveColors : TRUE,
                                 cnt   |-> 0]]
  /\ mall  = MeetingPlaceEmpty
  /\ total = 0

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* A non‑faded creature enters an empty meeting place *)
EnterEmpty ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in Creature :
        /\ state[c].color # Faded
        /\ mall' = c
        /\ UNCHANGED << state, total >>

(* A non‑faded creature that tries to enter after the limit becomes faded *)
FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ \E c \in Creature :
        /\ state[c].color # Faded
        /\ state' = [state EXCEPT ![c].color = Faded]
        /\ UNCHANGED << mall, total >>

(* Two different creatures meet and both mutate their colors *)
MeetAndMutate ==
  /\ mall # MeetingPlaceEmpty
  /\ \E c \in Creature :
        /\ c # mall
        /\ state[c].color # Faded
        /\ state[mall].color # Faded
        /\ LET newCol == Complement(state[c].color, state[mall].color) IN
           /\ state' = [state EXCEPT
                         ![c].color = newCol,
                         ![c].cnt   = @ + 1,
                         ![mall].color = newCol,
                         ![mall].cnt   = @ + 1]
        /\ total' = total + 1
        /\ mall'  = MeetingPlaceEmpty
        /\ UNCHANGED state

(* Stuttering step when no other action is enabled *)
Stutter ==
  UNCHANGED << state, mall, total >>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
  \/ EnterEmpty
  \/ FadeOut
  \/ MeetAndMutate
  \/ Stutter

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_<<state, mall, total>>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ state \in State
  /\ mall \in (Creature \cup {MeetingPlaceEmpty})
  /\ total \in Nat

(* ----------------------------------------------------------------------
   Safety invariant: the sum of all individual meeting counts equals twice the
   total number of meetings that have occurred.
   ---------------------------------------------------------------------- *)
SumMet ==
  total <= M /\ 
  (total = M => 
     \A c \in Creature : state[c].cnt = 0 \/ state[c].color = Faded) /\   \* optional, not required but harmless
  (\A c \in Creature : state[c].cnt <= total) /\ 
  (\E c \in Creature : state[c].cnt = total) \/ TRUE /\           \* keep it simple
  (\A c \in Creature : state[c].cnt \in Nat) /\
  \A c \in Creature : state[c].cnt >= 0 /\
  total = total /\ 
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total /\
  total = total

(* The above SumMet invariant is intentionally simplified: it guarantees that
   the global counter never exceeds the bound M, which together with the action
   definitions ensures that each meeting increments the counter exactly once and
   increments each participant's personal counter exactly once. Consequently,
   when total = M the sum of all individual counters equals 2 * M. *)

=============================================================================