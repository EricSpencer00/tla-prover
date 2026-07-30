---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME /\ N \in Nat /\ N > 0
       /\ M \in Nat /\ M > 0
       /\ Faded \in {Faded}

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}

Variable == [color : [Creatures -> Colors], attended : [Creatures -> Nat], place : Creatures \cup {MeetingPlaceEmpty}, total : Nat]

vars == <<Variable>>

RECURSIVE SumF(_, _)
SumF(f, S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE
                   IN f[x] + SumF(f, S \ {x})

TypeOK ==
    /\ Variable \in [color : [Creatures -> Colors],
                     attended : [Creatures -> Nat],
                     place : Creatures \cup {MeetingPlaceEmpty},
                     total : 0 .. M]

Init ==
    /\ Variable.color \in [Creatures -> Colors \ {Faded}]
    /\ Variable.attended = [c \in Creatures |-> 0]
    /\ Variable.place = MeetingPlaceEmpty
    /\ Variable.total = 0

EnterPlace(c) ==
    /\ Variable.place = MeetingPlaceEmpty
    /\ Variable.total < M
    /\ Variable.color[c] # Faded
    /\ Variable' = [Variable EXCEPT !.place = c]
    /\ UNCHANGED <<Variable.color, Variable.attended, Variable.total>>

FadeOut(c) ==
    /\ Variable.place = MeetingPlaceEmpty
    /\ Variable.total = M
    /\ Variable.color[c] # Faded
    /\ Variable' = [Variable EXCEPT !.color = [Variable.color EXCEPT ![c] = Faded]]
    /\ UNCHANGED <<Variable.attended, Variable.place, Variable.total>>

Complement(c1, c2) ==
    IF Variable.color[c1] = Variable.color[c2] THEN Variable.color[c1]
    ELSE LET s == {Variable.color[c1], Variable.color[c2]}
         IN CHOOSE x \in {"blue", "red", "yellow"} : x \notin s

MeetAndMutate(c) ==
    /\ Variable.place # MeetingPlaceEmpty
    /\ Variable.place # c
    /\ Variable.total < M
    /\ Variable.color[c] # Faded
    /\ Variable.attended[c] < M
    /\ Variable.attended[Variable.place] < M
    /\ LET newc == Complement(c, Variable.place)
       IN Variable' = [color |-> [Variable.color EXCEPT ![c] = newc, ![Variable.place] = newc],
                       attended |-> [Variable.attended EXCEPT ![c] = @ + 1, ![Variable.place] = @ + 1],
                       place |-> MeetingPlaceEmpty,
                       total |-> Variable.total + 1]
    /\ UNCHANGED <<>>

Next ==
    \/ \E c \in Creatures : EnterPlace(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet ==
    (Variable.total = M) => (SumF(Variable.attended, Creatures) = 2 * M)

====