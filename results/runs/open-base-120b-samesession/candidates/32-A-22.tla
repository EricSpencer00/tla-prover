---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*--------------------------------------------------------------------
  Colors
--------------------------------------------------------------------*)
Blue  == "blue"
Red   == "red"
Yellow== "yellow"

PrimaryColors == {Blue, Red, Yellow}
AllColors     == PrimaryColors \cup {Faded}

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Creatures == 1 .. N

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES state, mall, total

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
ColorOf(c) == state[c][1]
CountOf(c) == state[c][2]

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in PrimaryColors : c # c1 /\ c # c2

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ state \in [Creatures -> AllColors \times Nat]
  /\ \A c \in Creatures : CountOf(c) = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

EnterEmpty ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in Creatures :
        /\ ColorOf(c) # Faded
        /\ mall' = c
        /\ UNCHANGED <<state, total>>

FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ \E c \in Creatures :
        /\ ColorOf(c) # Faded
        /\ state' = [state EXCEPT ![c] = <<Faded, CountOf(c)>>]
        /\ UNCHANGED <<mall, total>>

MeetAndMutate ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E a \in Creatures :
        /\ a # mall
        /\ ColorOf(a) # Faded
        /\ ColorOf(mall) # Faded
        /\ LET newCol == Complement(ColorOf(a), ColorOf(mall)) IN
             /\ state' = [state EXCEPT
                           ![a]    = <<newCol, CountOf(a) + 1>>,
                           ![mall] = <<newCol, CountOf(mall) + 1>>]
             /\ mall'  = MeetingPlaceEmpty
             /\ total' = total + 1

Next ==
  \/ EnterEmpty
  \/ FadeOut
  \/ MeetAndMutate

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
vars == <<state, mall, total>>

Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
  /\ state \in [Creatures -> AllColors \times Nat]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  total = M => (SUM c \in Creatures : CountOf(c)) = 2 * M

(*--------------------------------------------------------------------
  Theorem (placeholder for model checker)
--------------------------------------------------------------------*)
THEOREM Spec => []TypeOK
THEOREM Spec => []SumMet

====