---- MODULE MCBoulanger ----
EXTENDS Boulanger, FiniteSets, Sequences, TLC

CONSTANT N, MaxNat

\* Override the natural numbers to a finite range
Nat == 0 .. MaxNat

\* Variables inherited from Boulanger
VARIABLES ticket, turn, state, queue

\* Initial state (same as Boulanger, but natural numbers are the finite set Nat)
Init ==
    /\ ticket = [i \in 1..N |-> 0]
    /\ turn = 0
    /\ state = [i \in 1..N |-> "Outside"]
    /\ queue = << >>

\* State constraint to keep ticket numbers strictly below MaxNat
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* Actions inherited from Boulanger (no modification)
Enter(i) ==
    /\ state[i] = "Outside"
    /\ state' = [state EXCEPT ![i] = "Trying"]
    /\ UNCHANGED << ticket, turn, queue >>

Assign(i) ==
    /\ state[i] = "Trying"
    /\ ticket' = [ticket EXCEPT ![i] = MaxNat + 1]
    /\ UNCHANGED << state, turn, queue >>

Wait(i) ==
    /\ state[i] = "Waiting"
    /\ UNCHANGED << ticket, state, turn, queue >>

Exit(i) ==
    /\ state[i] = "Critical"
    /\ state' = [state EXCEPT ![i] = "Outside"]
    /\ UNCHANGED << ticket, turn, queue >>

\* Next-state relation (sum over all processes)
Next ==
    \E i \in 1..N :
        \/ Enter(i)
        \/ Assign(i)
        \/ Wait(i)
        \/ Exit(i)

\* Specification used for model checking
Spec == Init /\ [][Next]_<<ticket, turn, state, queue>>

\* Safety invariants from Boulanger (assumed to be defined in the imported spec)
MutualExclusion == MutualExclusion
TypeOK == TypeOK
Inv == Inv

====