---- MODULE TLAPS ----
EXTENDS Integers

(* Backends configuration: the TLAPS backends that can be invoked to prove     *)
(* a subgoal, together with the default timeout and default tactics for each. *)
CONSTANTS zenon, isabelle, cvc3, yices, veriT, z3, spass, ls4, default

Backends == {zenon, isabelle, cvc3, yices, veriT, z3, spass, ls4}

Timeout == [b \in Backends |-> default]
Tactics == [b \in Backends |-> default]

\* A proof obligation is dispatched to a backend.  The state is the set of     *)
(* backend/time/tactic pairs that have been fired for this subgoal.            *)
Dispatch == [b : Backends, tm : Int, tk : Int]

Dispatched == [b \in Backends |-> [tm |-> default, tk |-> default]]

\* Backends subgoals are dispatched lazily, and nothing is ever taken back.   *)
\* Because the backends are pure provers, dispatching again with a different
(* timeout or tactic is exactly what a retry looks like -- no subgoal is ever
(* lost or cached across a retry of a different shape.                       *)
Fire(b) == Dispatched' = [Dispatched EXCEPT ![b] = [tm |-> Timeout[b], tk |-> Tactics[b]]]

Next == \E b \in Backends : Fire(b)

\* The invariance rule: an invariant preserved by every step of the system is
\* true at every reachable state.
InvarianceRule ==
    /\ \A x \in (Nat \X Nat) : x \in S <=> (x[1] \in Nat /\ x[2] \in Nat)
    /\ \A x \in S : x[1] \in Nat /\ x[2] \in Nat

\* Well-formedness of the form: the set of values of a function is a subset of
\* the declared codomain.
WellFormednessRule ==
    /\ \A x \in S : x[1] \in Nat /\ x[2] \in Nat
    /\ S \subseteq (Nat \X Nat)

\* Strong fairness: every back-and-forth step between the coordinator and a
\* single participant is eventually resolved the other way.
StrongFairness ==
    /\ \A x \in S : x[1] \in Nat /\ x[2] \in Nat
    /\ S \subseteq (Nat \X Nat)

\* Weak fairness: every step in which the coordinator advances is eventually
\* observed by some participant.
WeakFairness ==
    /\ \A x \in S : x[1] \in Nat /\ x[2] \in Nat
    /\ S \subseteq (Nat \X Nat)

\* Step simulation: every step the coordinator takes is faithfully reflected
\* in the shared record.
StepSimulation ==
    /\ \A x \in S : x[1] \in Nat /\ x[2] \in Nat
    /\ S \subseteq (Nat \X Nat)

\* Set extensionality: if two sets have the same elements they are the same.
SetExtensionality ==
    \A X \in SUBSET (Nat \X Nat) : \A Y \in SUBSET (Nat \X Nat) :
        (\A x \in X : x \in Y) /\ (\A x \in Y : x \in X) => X = Y

\* Non-universality: no set contains every possible value.
NoUniversalSet ==
    \A X \in SUBSET (Nat \X Nat) : X # (Nat \X Nat)

Spec == Next /\ InvarianceRule /\ WellFormednessRule
        /\ StrongFairness /\ WeakFairness /\ StepSimulation

Init == Dispatched = [b \in Backends |-> [tm |-> default, tk |-> default]]

SpecSimp == Init /\ [][Next]_Dispatched

Targets == {InvarianceRule, WellFormednessRule, StrongFairness,
            WeakFairness, StepSimulation}

\* The dispatch budget is not fixed, so fairness is per subgoal: once a
\* subgoal has been dispatched to a backend it stays dispatched for good.
EventualDispatch == \A r \in Targets : <>(Dispatched[r] # [tm |-> default, tk |-> default])

====