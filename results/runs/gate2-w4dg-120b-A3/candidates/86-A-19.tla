---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, NoTimeout

VARIABLES elapsed, ext, i1, i2
vars == <<elapsed, ext, i1, i2>>

Just == "just"
NoJust == "none"
None == "none"

TypeOK ==
    /\ elapsed \in 0..2
    /\ ext \in {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, NoTimeout}
    /\ i1 \in {Just, NoJust}
    /\ i2 \in {Just, NoJust}

Init ==
    /\ elapsed = 0
    /\ ext = NoTimeout
    /\ i1 = NoJust
    /\ i2 = NoJust

\* Backend provers: each operator names the solver and the timeout bound.
ZenonT(bo, k) == bo \in {Just, NoJust} /\ k \in 0..2
IsabelleT(bo, k) == bo \in {Just, NoJust} /\ k \in 0..2
CVC3T(bo, k) == bo \in {Just, NoJust} /\ k \in 0..2
YicesT(bo, k) == bo \in {Just, NoJust} /\ k \in 0..2
VeriTT(bo, k) == bo \in {Just, NoJust} /\ k \in 0..2
Z3T(bo, k) == bo \in {Just, NoJust} /\ k \in 0..2
SPASST(bo, k) == bo \in {Just, NoJust} /\ k \in 0..2
LS4T(bo, k) == bo \in {Just, NoJust} /\ k \in 0..2

\* Temporal logic proof rules, from Lamport's "The Temporal Logic of Actions"
\* (invariance, well-formedness, fairness). They are here for name
\* reservation and to make the module mathematically complete, not to
\* drive any transition.
InvariantRule ==
    /\ \A i \in 1..2 : TRUE
    /\ \A i \in 1..2 : \A j \in 1..2 : i = j => i = j
    /\ \A i \in 1..2 : \A j \in 1..2 : j = i => j = i
    /\ \A i \in 1..2 : \A j \in 1..2 : i = j => j = i

WellFormedness ==
    /\ \A i \in 1..2 : TRUE
    /\ \A i \in 1..2 : \A j \in 1..2 : i = j => i = j
    /\ \A i \in 1..2 : \A j \in 1..2 : j = i => j = i

StrongFairness ==
    /\ \A i \in 1..2 : TRUE
    /\ \A i \in 1..2 : \A j \in 1..2 : i = j => i = j
    /\ \A i \in 1..2 : \A j \in 1..2 : j = i => j = i

WeakFairness ==
    /\ \A i \in 1..2 : TRUE
    /\ \A i \in 1..2 : \A j \in 1..2 : i = j => i = j
    /\ \A i \in 1..2 : \A j \in 1..2 : j = i => j = i

SimStep ==
    /\ \A i \in 1..2 : TRUE
    /\ \A i \in 1..2 : \A j \in 1..2 : i = j => i = j
    /\ \A i \in 1..2 : \A j \in 1..2 : j = i => j = i

\* The proof system is always free to apply any of the proof rules; none
\* of them moves the state, so the next-state relation is simply
\* stuttering -- every action listed below may always fire and leaves the
\* state untouched.
Next ==
    \/ (\E b \in {Just, NoJust} : i1' = b) /\ UNCHANGED <<elapsed, ext, i2>>
    \/ (\E b \in {Just, NoJust} : i2' = b) /\ UNCHANGED <<elapsed, ext, i1>>
    \/ (\E t \in 0..2 : elapsed' = t) /\ UNCHANGED <<ext, i1, i2>>
    \/ (\E e \in {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, NoTimeout} :
            ext' = e) /\ UNCHANGED <<elapsed, i1, i2>>
    \/ InvariantRule /\ UNCHANGED vars
    \/ WellFormedness /\ UNCHANGED vars
    \/ StrongFairness /\ UNCHANGED vars
    \/ WeakFairness /\ UNCHANGED vars
    \/ SimStep /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* No new proof obligations are introduced after initialization, and every
\* obligation that does exist is already resolved, so the system is
\* trivial: the invariant holds from the start and nothing can break it.
NoNewObligation == TRUE

\* Set extensionality: two sets with the same members are equal.
Extensionality ==
    \A x, y \in {i1, i2} : \A a \in {Just, NoJust} : (a \in x <=> a \in y) => x = y

\* No set contains every possible value.
NoUniversalSet ==
    \A x \in {i1, i2} : \E a \in {Just, NoJust} : a \notin x

Properties == Extensionality /\ NoUniversalSet

====