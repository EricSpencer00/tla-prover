---- MODULE Chameneos ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants (to be bound in the .cfg file)
-----------------------------------------------------------------*)
CONSTANT N            \* number of creatures
CONSTANT M            \* total meetings limit
CONSTANT Faded        \* the special color representing a faded creature
CONSTANT MeetingPlaceEmpty

(*-----------------------------------------------------------------
  Sets
-----------------------------------------------------------------*)
Colors == {"blue", "red", "yellow", Faded}
Creatures == 1..N

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES state, mall, totalMeetings

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
(* state maps each creature to a pair [color, meetCount] *)
Color(c) == state[c][1]
MeetCount(c) == state[c][2]

(* Complement (mutation) rule for two colors *)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    CASE c1 = "blue" /\ c2 = "red"   : "yellow" [] 
         c1 = "red"  /\ c2 = "blue"  : "yellow" [] 
         c1 = "blue" /\ c2 = "yellow": "red"    [] 
         c1 = "yellow" /\ c2 = "blue": "red"    [] 
         c1 = "red"  /\ c2 = "yellow": "blue"   [] 
         c1 = "yellow" /\ c2 = "red" : "blue"   [] 
         OTHER                        : Faded   \* should never happen

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in {"blue", "red", "yellow"} : TRUE,
                                   meetCount |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = 0

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
EnterEmpty ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E c \in Creatures :
        /\ Color(c) # Faded
        /\ mall' = c
        /\ UNCHANGED << state, totalMeetings >>

FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ \E c \in Creatures :
        /\ Color(c) # Faded
        /\ state' = [state EXCEPT ![c].color = Faded]
        /\ UNCHANGED << mall, totalMeetings >>

MeetAndMutate ==
  /\ mall # MeetingPlaceEmpty
  /\ \E c \in Creatures :
        /\ c # mall
        /\ Color(c) # Faded
        /\ LET newCol == Complement(Color(c), Color(mall)) IN
           /\ state' = [state EXCEPT 
                         ![c].color = newCol,
                         ![c].meetCount = @ + 1,
                         ![mall].color = newCol,
                         ![mall].meetCount = @ + 1]
           /\ mall' = MeetingPlaceEmpty
           /\ totalMeetings' = totalMeetings + 1

\* No other state changes are allowed
OtherStutter ==
  UNCHANGED << state, mall, totalMeetings >>

Next ==
  \/ EnterEmpty
  \/ FadeOut
  \/ MeetAndMutate
  \/ OtherStutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<state, mall, totalMeetings>>

(*-----------------------------------------------------------------
  Type correctness invariant (not the safety property required)
-----------------------------------------------------------------*)
TypeOK ==
  /\ state \in [Creatures -> [color : Colors, meetCount : Nat]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in Nat

(*-----------------------------------------------------------------
  Safety invariant: sum of individual meeting counts equals twice the
  total number of meetings once the limit is reached.
-----------------------------------------------------------------*)
SumMet ==
  (totalMeetings >= M) => 
    ( \A c \in Creatures : MeetCount(c) = MeetCount("Total") )
  /\ 
  ( totalMeetings >= M => 
      ( +\sum c \in Creatures : MeetCount(c) ) = 2 * totalMeetings)

(* An auxiliary definition to compute the sum without exposing it
   as a variable; used only inside SumMet. *)
MeetCount("Total") == 
  IF totalMeetings >= M THEN
    LET s == +\sum c \in Creatures : MeetCount(c) IN s / 2
  ELSE 0

=============================================================================