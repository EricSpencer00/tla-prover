---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

(*-----------------------------------------------------------------
  Constants supplied by the .cfg file
-----------------------------------------------------------------*)
CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*-----------------------------------------------------------------
  Basic sets and derived constants
-----------------------------------------------------------------*)
Creatures == 1..N

Blue == "Blue"
Red  == "Red"
Yellow == "Yellow"

Colors == {Blue, Red, Yellow, Faded}

NonFadedColors == {Blue, Red, Yellow}

(*-----------------------------------------------------------------
  Complement rule
-----------------------------------------------------------------*)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CASE
      /\ {c1, c2} = {Blue, Red}    -> Yellow
      [] /\ {c1, c2} = {Red, Yellow} -> Blue
      [] /\ {c1, c2} = {Blue, Yellow} -> Red
    ENDCASE

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES creatures, mall, total

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ mall = MeetingPlaceEmpty
  /\ total = 0
  /\ creatures = [c \in Creatures |-> 
        [ color |-> CHOOSE col \in NonFadedColors : TRUE,
          count |-> 0 ]]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)

Enter ==
  \E c \in Creatures :
    /\ creatures[c].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ mall' = c
    /\ creatures' = creatures
    /\ total' = total

FadeOut ==
  \E c \in Creatures :
    /\ creatures[c].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ mall' = MeetingPlaceEmpty
    /\ creatures' = [creatures EXCEPT ![c] = 
          [color |-> Faded,
           count |-> creatures[c].count]]
    /\ total' = total

Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ LET w == mall IN
       /\ creatures[w].color # Faded
       /\ \E a \in Creatures :
            /\ a # w
            /\ creatures[a].color # Faded
            /\ LET newcol == Complement(creatures[w].color,
                                        creatures[a].color) IN
                 /\ creatures' = [creatures EXCEPT
                                    ![w] = [color |-> newcol,
                                            count |-> creatures[w].count + 1],
                                    ![a] = [color |-> newcol,
                                            count |-> creatures[a].count + 1]]
                 /\ mall' = MeetingPlaceEmpty
                 /\ total' = total + 1

Next ==
  \/ Enter
  \/ FadeOut
  \/ Meet

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
vars == <<creatures, mall, total>>

Spec ==
  Init /\ [] [Next]_vars

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
  /\ mall \in {MeetingPlaceEmpty} \cup Creatures
  /\ total \in Nat
  /\ total <= M
  /\ creatures \in [Creatures -> [color: Colors, count: Nat]]
  /\ \A c \in Creatures :
        creatures[c].color \in Colors
        /\ creatures[c].count \in Nat

SumMet ==
  (total = M) => ( 
        (\\ sum == \Sum c \in Creatures : creatures[c].count ;
         sum) = 2 * M)

(*-----------------------------------------------------------------
  Theorems (optional)
-----------------------------------------------------------------*)
THEOREM Spec => []TypeOK
THEOREM Spec => []SumMet

====