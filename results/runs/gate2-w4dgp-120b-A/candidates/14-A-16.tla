---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS
    N,
    MaxNat

VARIABLES
    pi, pj, pstate, pnext, pwait

vars == << pi, pj, pstate, pnext, pwait >>

\* Finite range for the natural-number override in the .cfg: this replaces the
\* unbounded Naturals Nat with a bounded version that is external to the
\* module.  EXTENDS Naturals stays so that the symbolic Nat operator can still
\* be used inside the module, while the model-checking configuration swaps it
\* out for NatOverride.

Range == 0..MaxNat

TypeOK ==
    /\ pi \in [1..N -> Range]
    /\ pj \in [1..N -> Range]
    /\ pstate \in [1..N -> {"idle", "trying", "critical", "exiting"}]
    /\ pnext \subseteq 1..N
    /\ pwait \subseteq 1..N

MutualExclusion ==
    \A i \in 1..N : pstate[i] = "critical" => \A j \in 1..N : (j # i) => pstate[j] # "critical"

Init ==
    /\ pi = [i \in 1..N |-> 0]
    /\ pj = [i \in 1..N |-> 0]
    /\ pstate = [i \in 1..N |-> "idle"]
    /\ pnext = {}
    /\ pwait = {}

\* A process takes a ticket and joins the waiting set.
Want(i) ==
    /\ pstate[i] = "idle"
    /\ pstate' = [pstate EXCEPT ![i] = "trying"]
    /\ pi' = [pi EXCEPT ![i] = pj[i]]
    /\ pwait' = pwait \cup {i}
    /\ UNCHANGED << pj, pnext >>

\* Ticket-numbered entry: it enters only by strictly winning the race.
Enter(i) ==
    /\ pstate[i] = "trying"
    /\ i \in pwait
    /\ \A j \in pwait :
        (i < j) => (pi[i] < pj[j])
    /\ pstate' = [pstate EXCEPT ![i] = "critical"]
    /\ UNCHANGED << pi, pj, pnext, pwait >>

\* Exit from the critical section.
Exit(i) ==
    /\ pstate[i] = "critical"
    /\ pstate' = [pstate EXCEPT ![i] = "exiting"]
    /\ UNCHANGED << pi, pj, pnext, pwait >>

\* A slow process re-samples its peer ticket and stays in the trying state.
ReSample(i) ==
    /\ pstate[i] = "trying"
    /\ pj' = [pj EXCEPT ![i] = pi[i]]
    /\ UNCHANGED << pi, pstate, pnext, pwait >>

\* Release the critical section.
Idle(i) ==
    /\ pstate[i] = "exiting"
    /\ pstate' = [pstate EXCEPT ![i] = "idle"]
    /\ pwait' = pwait \ {i}
    /\ UNCHANGED << pi, pj, pnext >>

Next ==
    \/ \E i \in 1..N : Want(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)
    \/ \E i \in 1..N : ReSample(i)
    \/ \E i \in 1..N : Idle(i)

Spec == Init /\ [][Next]_vars

\* The invariant is the full set from the source; putting it here keeps the
\* reference .cfg's INVARIANTS list simple.
Inv == TypeOK /\ MutualExclusion

StateConstraint == \A i \in 1..N : pi[i] < MaxNat

====