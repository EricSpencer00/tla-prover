---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

(* ----------------------------------------------------------------------
   Constants (to be instantiated in the .cfg)
   ---------------------------------------------------------------------- *)
CONSTANT N               \* number_of_creatures
CONSTANT M               \* total_meetings_limit
CONSTANT Faded           \* the special faded color
CONSTANT MeetingPlaceEmpty

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
Colors == {"blue", "red", "yellow", Faded}
Creatures == 1 .. N

(* ----------------------------------------------------------------------
   Type definitions
   ---------------------------------------------------------------------- *)
CREATURE == [color : Colors, count : Nat]

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES creatureState, waiting, total

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ creatureState = [c \in Creatures |-> [color |-> CHOOSE col \in {"blue", "red", "yellow"} : TRUE,
                                            count |-> 0]]
    /\ waiting = MeetingPlaceEmpty
    /\ total = 0

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

\* Complement rule: given two colors, returns the resulting color for both.
Complement(col1, col2) ==
    IF col1 = col2 THEN col1
    ELSE CHOOSE c \in Colors \ {col1, col2} : c

EnterEmpty(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ total < M
    /\ creatureState[c].color # Faded
    /\ waiting' = c
    /\ UNCHANGED <<creatureState, total>>

FadeOut(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ total = M
    /\ creatureState[c].color # Faded
    /\ creatureState' = [creatureState EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<waiting, total>>

MeetAndMutate(c) ==
    /\ waiting # MeetingPlaceEmpty
    /\ waiting # c
    /\ creatureState[c].color # Faded
    /\ creatureState[waiting].color # Faded
    /\ LET newCol == Complement(creatureState[c].color, creatureState[waiting].color) IN
       /\ creatureState' = [creatureState EXCEPT
                               ![c].color = newCol,
                               ![c].count = @ + 1,
                               ![waiting].color = newCol,
                               ![waiting].count = @ + 1]
    /\ waiting' = MeetingPlaceEmpty
    /\ total' = total + 1

Next ==
    \/ \E c \in Creatures : EnterEmpty(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<creatureState, waiting, total>>

(* ----------------------------------------------------------------------
   Type correctness invariant (not required but useful)
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ creatureState \in [Creatures -> CREATURE]
    /\ waiting \in (Creatures \cup {MeetingPlaceEmpty})
    /\ total \in Nat

(* ----------------------------------------------------------------------
   Safety invariant required by the description
   ---------------------------------------------------------------------- *)
SumMet ==
    (total = M) => 
        (/\ \A c \in Creatures : creatureState[c].count <= M
         /\ \E s \in Nat : s = 2 * M /\ \A c \in Creatures : creatureState[c].count = s
         /\ \A c \in Creatures : creatureState[c].color \in Colors)

(* ----------------------------------------------------------------------
   The list of required identifiers
   ---------------------------------------------------------------------- *)
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT SumMet

====