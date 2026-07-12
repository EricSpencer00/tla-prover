---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES C, MP, G

\*----------------------------------------------------
\* Type definitions
\*----------------------------------------------------
Color == {"blue", "red", "yellow", Faded}
Creature == 1..N

\*----------------------------------------------------
\* Definition of the complement rule
\*----------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        LET colors == {"blue", "red", "yellow"} IN
        FIRST colors \ {c1, c2}

\*----------------------------------------------------
\* Initial state
\*----------------------------------------------------
Init ==
    /\ C \in [Creature |-> [color : Color \ {Faded}, meets : Nat]]
    /\ \A i \in Creature : C[i] = [color |-> CHOOSE c \In {"blue", "red", "yellow"} : TRUE,
                                  meets |-> 0]
    /\ MP = MeetingPlaceEmpty
    /\ G = 0

\*----------------------------------------------------
\* Actions
\*----------------------------------------------------
EnterEmpty ==
    /\ MP = MeetingPlaceEmpty
    /\ G < M
    /\ \E i \in Creature : C[i].color \in {"blue", "red", "yellow"} /\ MP' = i
    /\ UNCHANGED <<C, G>>

FadeOut ==
    /\ MP = MeetingPlaceEmpty
    /\ G = M
    /\ \E i \in Creature : C[i].color \in {"blue", "red", "yellow"} /\ 
       C' = [C EXCEPT ![i].color = Faded]
    /\ UNCHANGED <<MP, G>>

MeetMutate ==
    /\ MP \in Creature
    /\ \E i \in Creature : i # MP
    /\ \E j \in Creature : j # MP /\ i = MP \/ j = MP
    /\ \E i, j \in Creature :
          i # j /\ 
          MP = i /\ 
          \E r \in {"blue", "red", "yellow"} :
                r \in {C[i].color, C[j].color} =>
                  LET c1 == C[i].color, c2 == C[j].color IN
                   /\ C' = [C EXCEPT ![i].color = Complement(c1, c2),
                               ![j].color = Complement(c1, c2),
                               ![i].meets = C[i].meets + 1,
                               ![j].meets = C[j].meets + 1]
                   /\ MP' = MeetingPlaceEmpty
                   /\ G' = G + 1
    /\ UNCHANGED G

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetMutate

\*----------------------------------------------------
\* Specification
\*----------------------------------------------------
Spec ==
    Init /\ [][Next]_<<C, MP, G>>

\*----------------------------------------------------
\* Type correctness invariant
\*----------------------------------------------------
TypeOK ==
    /\ C \in [Creature |-> [color : Color, meets : Nat]]
    /\ MP \in Creature \/ MP = MeetingPlaceEmpty
    /\ G \in Nat
    /\ G <= M

\*----------------------------------------------------
\* Safety invariant: sum of individual meets equals twice global meets
\*----------------------------------------------------
SumMet ==
    /\ Sum(\lambda i \in Creature : C[i].meets) = 2 * G

====