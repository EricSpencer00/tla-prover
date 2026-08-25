---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty
CONSTANTS Blue, Red, Yellow

Color == {Blue, Red, Yellow, Faded}

(* Complement rule: same color stays, different colors both become the third color *)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    CASE c1 = Blue /\ c2 = Red   -> Yellow,
         c1 = Red /\ c2 = Blue   -> Yellow,
         c1 = Blue /\ c2 = Yellow -> Red,
         c1 = Yellow /\ c2 = Blue -> Red,
         c1 = Red /\ c2 = Yellow -> Blue,
         c1 = Yellow /\ c2 = Red -> Blue,
         OTHER -> Faded  \* should never occur

VARIABLES cstate, Place, total

(* Type correctness invariant *)
TypeOK ==
  /\ cstate \in [1..N -> [color : Color, meetCount : Nat]]
  /\ Place \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat

(* Initial state: each creature gets a nondeterministic non‑faded color, count 0 *)
Init ==
  /\ cstate = [i \in 1..N |-> [color |-> CHOOSE col \in Color \ {Faded} : TRUE,
                               meetCount |-> 0]]
  /\ Place = MeetingPlaceEmpty
  /\ total = 0

(* A non‑faded creature enters an empty meeting place while meetings remain *)
Enter(c) ==
  /\ Place = MeetingPlaceEmpty
  /\ total < M
  /\ c \in 1..N
  /\ cstate[c].color # Faded
  /\ Place' = c
  /\ UNCHANGED <<cstate, total>>

(* After the limit is reached, a creature trying to enter fades out *)
FadeOut(c) ==
  /\ Place = MeetingPlaceEmpty
  /\ total = M
  /\ c \in 1..N
  /\ cstate[c].color # Faded
  /\ cstate' = [cstate EXCEPT ![c].color = Faded]
  /\ Place' = MeetingPlaceEmpty
  /\ UNCHANGED total

(* Two different non‑faded creatures meet, mutate colors, and update counters *)
Meet(c) ==
  LET w == Place IN
  /\ Place # MeetingPlaceEmpty
  /\ total < M
  /\ c \in 1..N
  /\ c # w
  /\ cstate[c].color # Faded
  /\ cstate[w].color # Faded
  /\ newColor = Complement(cstate[c].color, cstate[w].color)
  /\ cstate' = [cstate EXCEPT
                  ![c].color = newColor,
                  ![c].meetCount = @ + 1,
                  ![w].color = newColor,
                  ![w].meetCount = @ + 1]
  /\ total' = total + 1
  /\ Place' = MeetingPlaceEmpty

Next ==
  \/ \E c \in 1..N: Enter(c)
  \/ \E c \in 1..N: FadeOut(c)
  \/ \E c \in 1..N: Meet(c)

Spec == Init /\ [][Next]_<<cstate, Place, total>>

(* Safety invariant: when the global counter reaches the limit,
   the sum of individual meeting counts equals twice that limit *)
SumMet ==
  /\ total = M
  /\ (∑ i \in 1..N: cstate[i].meetCount) = 2 * M

====