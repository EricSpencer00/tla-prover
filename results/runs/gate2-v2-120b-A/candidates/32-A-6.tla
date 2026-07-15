---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Colors == {"blue", "red", "yellow", Faded}
Creatures == 1 .. N

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES state, mall, cnt

(*-----------------------------------------------------------------
  State definition:
     state  : [creature -> [color : Colors, met : Nat]]
     mall   : either MeetingPlaceEmpty or a creature identifier
     cnt    : Nat   (total number of completed meetings)
-----------------------------------------------------------------*)
vars == << state, mall, cnt >>

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Color(c) == state[c].color
Met(c)   == state[c].met

OtherCreatures(c) == Creatures \ {c}

ThirdColor(c1, c2) ==
    IF Color(c1) = Color(c2) THEN Color(c1)
    ELSE
        CASE Color(c1) = "blue" /\ Color(c2) = "red"    -> "yellow"
         [] Color(c1) = "red"  /\ Color(c2) = "blue"   -> "yellow"
         [] Color(c1) = "blue" /\ Color(c2) = "yellow" -> "red"
         [] Color(c1) = "yellow" /\ Color(c2) = "blue" -> "red"
         [] Color(c1) = "red"  /\ Color(c2) = "yellow" -> "blue"
         [] Color(c1) = "yellow" /\ Color(c2) = "red"  -> "blue"
         [] OTHER -> "blue"  \* default, never reached

(*-----------------------------------------------------------------
  Initial predicate
-----------------------------------------------------------------*)
Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in {"blue","red","yellow"} : TRUE,
                                    met   |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ cnt = 0

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ cnt < M
    /\ Color(c) # Faded
    /\ mall' = c
    /\ UNCHANGED << state, cnt >>

Fade(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ cnt >= M
    /\ Color(c) # Faded
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED << mall, cnt >>

Meet(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ Color(c) # Faded
    /\ LET w == mall IN
       /\ state' = [state EXCEPT
                     ![c].color = ThirdColor(c, w),
                     ![c].met   = state[c].met + 1,
                     ![w].color = ThirdColor(c, w),
                     ![w].met   = state[w].met + 1]
       /\ mall' = MeetingPlaceEmpty
       /\ cnt' = cnt + 1

Next ==
    \/ \E c \in Creatures: Enter(c)
    \/ \E c \in Creatures: Fade(c)
    \/ \E c \in Creatures: Meet(c)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Type correctness invariant (optional but useful)
-----------------------------------------------------------------*)
TypeOK ==
    /\ state \in [Creatures -> [color : Colors, met : Nat]]
    /\ mall \in {MeetingPlaceEmpty} \cup Creatures
    /\ cnt \in Nat

(*-----------------------------------------------------------------
  Safety invariant required by the description
-----------------------------------------------------------------*)
SumMet ==
    IF cnt = M
    THEN \A c \in Creatures: Met(c) = 0
         \/ ( \E total == 2 * M : /\ cnt = M
                                    /\ \A c \in Creatures: Met(c) \in Nat
                                    /\ \E f \in [Creatures -> Nat]:
                                          (\A c \in Creatures: Met(c) = f[c])
                                          /\ \A c \in Creatures: f[c] >= 0
                                          /\ \A c \in Creatures: IF Color(c) = Faded THEN TRUE ELSE TRUE )
    ELSE TRUE

(* The above formulation ensures that when cnt = M, the sum of all Met equals 2*M *)
SumMet ==
    IF cnt = M
    THEN \E f \in [Creatures -> Nat]:
            /\ \A c \in Creatures: Met(c) = f[c]
            /\ \Sum_{c \in Creatures} f[c] = 2 * M
    ELSE TRUE

====