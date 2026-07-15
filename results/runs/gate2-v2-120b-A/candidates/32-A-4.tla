---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* the special faded color
    MeetingPlaceEmpty \* value representing an empty meeting place

\* Colors (including the special faded color)
Colors == {"blue", "red", "yellow", Faded}
NormalColors == {"blue", "red", "yellow"}

\* The set of creature identifiers
Creatures == 1..N

\* State variables
VARIABLES state, mall, total

\* A state is a function mapping each creature to a tuple <<color, count>>
State == [c \in Creatures |-> <<NormalColors, 0>>]

\* Initial predicate
Init ==
    /\ state = [c \in Creatures |-> <<Choose(NormalColors), 0>>]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* Complement rule: given two colors, return the color both will adopt
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        CASE c1 = "blue" /\ c2 = "red"   -> "yellow" [] 
             c1 = "red" /\ c2 = "blue"   -> "yellow" [] 
             c1 = "blue" /\ c2 = "yellow"-> "red" [] 
             c1 = "yellow" /\ c2 = "blue"-> "red" [] 
             c1 = "red" /\ c2 = "yellow" -> "blue" [] 
             c1 = "yellow" /\ c2 = "red" -> "blue" []

\* Helper to check if a creature is faded
IsFaded(c) == state[c][1] = Faded

\* Action: a non‑faded creature enters an empty meeting place before the limit is reached
EnterEmpty ==
    /\ total < M
    /\ mall = MeetingPlaceEmpty
    /\ \E c \in Creatures :
          /\ ~IsFaded(c)
          /\ state' = [state EXCEPT ![c] = state[c]]
          /\ mall' = c
          /\ total' = total
    /\ UNCHANGED << >>

\* Action: a non‑faded creature fades out when the limit has been reached and the mall is empty
FadeOut ==
    /\ total >= M
    /\ mall = MeetingPlaceEmpty
    /\ \E c \in Creatures :
          /\ ~IsFaded(c)
          /\ state' = [state EXCEPT ![c][1] = Faded]
          /\ mall' = MeetingPlaceEmpty
          /\ total' = total
    /\ UNCHANGED << >>

\* Action: two different creatures meet and mutate
MeetAndMutate ==
    /\ mall # MeetingPlaceEmpty
    /\ \E c_a \in Creatures :
         /\ c_a # mall               \* cannot meet itself
         /\ ~IsFaded(c_a)
         /\ ~IsFaded(mall)
         /\ LET c1 == state[mall][1] IN
            LET c2 == state[c_a][1] IN
            LET newColor == Complement(c1, c2) IN
            /\ state' = [state EXCEPT 
                           ![mall] = <<newColor, state[mall][2] + 1>>,
                           ![c_a]  = <<newColor, state[c_a][2] + 1>>]
         /\ mall' = MeetingPlaceEmpty
         /\ total' = total + 1
    /\ UNCHANGED << >>

\* Stuttering step to avoid deadlock after termination
Stutter ==
    /\ state' = state
    /\ mall' = mall
    /\ total' = total

\* Next-state relation
Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate
    \/ Stutter

\* Safety invariant: all variables stay within their domains
TypeOK ==
    /\ state \in [Creatures -> <<Colors, Nat>>]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat

\* Safety invariant required by the description
SumMet ==
    (total = M) => 
        ( \A c \in Creatures : state[c][2] >= 0 ) /\ 
        ( \E sum == 2 * M : 
            sum = ( +\sum_{c \in Creatures} state[c][2] ) /\ sum = 2 * M )

\* Specification
Spec == Init /\ [][Next]_<<state, mall, total>>

\* The name of the invariant as required by the cfg file
SafetyInvariant == SumMet

====