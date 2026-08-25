---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*--------------------------------------------------------------------
  Colors
--------------------------------------------------------------------*)
Color == {"blue", "red", "yellow", Faded}
NonFadedColor == {"blue", "red", "yellow"}

(*--------------------------------------------------------------------
  Complement rule
--------------------------------------------------------------------*)
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CASE
          /\ (c1 = "blue"  /\ c2 = "red")  \/ (c1 = "red"   /\ c2 = "blue")   -> "yellow"
          /\ (c1 = "red"   /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "red") -> "blue"
          /\ (c1 = "blue"  /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") -> "red"
        [] OTHER -> Faded \* (should never happen)
        ENDCASE

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES Creatures, Mall, Total

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ Creatures \in [1..N -> [color : NonFadedColor, cnt : Nat]]
    /\ \A i \in 1..N: Creatures[i].cnt = 0
    /\ Mall = MeetingPlaceEmpty
    /\ Total = 0

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
EnterEmpty ==
    /\ Mall = MeetingPlaceEmpty
    /\ Total < M
    /\ \E i \in 1..N:
        /\ Creatures[i].color # Faded
        /\ Mall' = i
        /\ Creatures' = Creatures
        /\ Total' = Total

FadeOut ==
    /\ Mall = MeetingPlaceEmpty
    /\ Total >= M
    /\ \E i \in 1..N:
        /\ Creatures[i].color # Faded
        /\ Mall' = MeetingPlaceEmpty
        /\ Creatures' = [Creatures EXCEPT ![i].color = Faded]
        /\ Total' = Total

MeetAndMutate ==
    /\ Mall \in 1..N
    /\ Total < M
    /\ \E i \in 1..N:
        /\ i # Mall
        /\ Creatures[i].color # Faded
        /\ Creatures[Mall].color # Faded
        LET newc == Complement(Creatures[i].color, Creatures[Mall].color) IN
          /\ Creatures' = [Creatures EXCEPT
                             ![i]     = [color |-> newc, cnt |-> Creatures[i].cnt + 1],
                             ![Mall]  = [color |-> newc, cnt |-> Creatures[Mall].cnt + 1]]
          /\ Total' = Total + 1
          /\ Mall' = MeetingPlaceEmpty

Next == \/ EnterEmpty \/ FadeOut \/ MeetAndMutate

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Creatures, Mall, Total>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ Creatures \in [1..N -> [color : Color, cnt : Nat]]
    /\ Mall \in (MeetingPlaceEmpty \/ 1..N)
    /\ Total \in Nat
    /\ Total <= M

SumMet ==
    (Total = M) => (\Sum i \in 1..N: Creatures[i].cnt) = 2 * M

====