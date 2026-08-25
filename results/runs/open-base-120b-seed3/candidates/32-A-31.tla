---- MODULE Chameneos ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants (provided by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*-----------------------------------------------------------------
  Color definitions
-----------------------------------------------------------------*)
CONSTANTS Blue, Red, Yellow
ASSUME ColorSet = {Blue, Red, Yellow, Faded}
ASSUME /\ Blue # Red /\ Blue # Yellow /\ Red # Yellow
ASSUME Faded \in ColorSet

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES creatures, mall, total

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
Color(c) == c \in ColorSet
Count(n) == n \in Nat

CreatureRec(c) == 
    [color : ColorSet,
     meetings : Nat]

TypeOK ==
    /\ creatures \in [1..N -> CreatureRec]
    /\ \A i \in 1..N :
          /\ Color(creatures[i].color)
          /\ Count(creatures[i].meetings)
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M

(*-----------------------------------------------------------------
  Complement rule
-----------------------------------------------------------------*)
Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE
        CASE /\ {c1, c2} = {Blue, Red}   -> Yellow
          [] /\ {c1, c2} = {Red, Yellow} -> Blue
          [] /\ {c1, c2} = {Blue, Yellow}-> Red
          [] OTHER -> Faded   \* should never happen

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ total = 0
    /\ mall = MeetingPlaceEmpty
    /\ creatures = [i \in 1..N |-> 
          [color    |-> ChooseColor,
           meetings |-> 0]]
    
(* nondeterministic choice of an initial color (non‑faded) *)
ChooseColor == 
    CHOOSE c \in {Blue, Red, Yellow} : TRUE

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
Enter ==
    /\ total < M
    /\ mall = MeetingPlaceEmpty
    /\ \E c \in 1..N :
          /\ creatures[c].color # Faded
          /\ mall' = c
          /\ UNCHANGED <<creatures, total>>
          /\ c # c   \* trivial, just to bind the existential

Fade ==
    /\ total >= M
    /\ mall = MeetingPlaceEmpty
    /\ \E c \in 1..N :
          /\ creatures[c].color # Faded
          /\ creatures' = [creatures EXCEPT ![c].color = Faded]
          /\ UNCHANGED <<mall, total>>

Meet ==
    /\ total < M
    /\ \E w \in 1..N :
          /\ mall = w
          /\ \E c \in 1..N :
                /\ c # w
                /\ creatures[c].color # Faded
                /\ creatures[w].color # Faded
                /\ LET newCol == Complement(creatures[c].color,
                                            creatures[w].color) IN
                   /\ creatures' = [creatures EXCEPT 
                          ![c].color = newCol,
                          ![c].meetings = @ + 1,
                          ![w].color = newCol,
                          ![w].meetings = @ + 1]
                /\ total' = total + 1
                /\ mall' = MeetingPlaceEmpty
                /\ UNCHANGED <<>>

Next == \/ Enter \/ Fade \/ Meet

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<creatures, mall, total>>

(*-----------------------------------------------------------------
  Safety property: sum of meetings equals 2*M when total = M
-----------------------------------------------------------------*)
SumMeetings ==
    Sum({i \in 1..N : creatures[i].meetings})

SumMet ==
    total = M => SumMeetings = 2 * M

====