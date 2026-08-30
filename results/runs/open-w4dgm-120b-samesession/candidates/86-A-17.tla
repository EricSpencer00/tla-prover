---- MODULE TLAPS ----
EXTENDS Naturals, Sequences

(* Backend provers for the TLA proof system.  The operators below are      *)
(* configuration directives for TLAPS; they do not change any state.       *)
\* They are named for their provers and name the timeout used.            *)
\* The rule operators below are the temporal-logic proof rules from Lamport's 2018 paper. *)

CONSTANTS NoBackend, NoTactic

\* Dispatch a proof obligation to the Zenon prover, with a timeout in seconds.
Zenon(t) == [backend |-> "Zenon", timeout |-> t, tactic |-> NoTactic]

\* Dispatch a proof obligation to the Isabelle prover, with a timeout in seconds.
Isabelle(t) == [backend |-> "Isabelle", timeout |-> t, tactic |-> NoTactic]

\* Dispatch a proof obligation to the CVC3 SMT solver, with a timeout in seconds.
CVC3(t) == [backend |-> "CVC3", timeout |-> t, tactic |-> NoTactic]

\* Dispatch a proof obligation to the Yices SMT solver, with a timeout in seconds.
Yices(t) == [backend |-> "Yices", timeout |-> t, tactic |-> NoTactic]

\* Dispatch a proof obligation to the veriT SMT solver, with a timeout in seconds.
VeriT(t) == [backend |-> "veriT", timeout |-> t, tactic |-> NoTactic]

\* Dispatch a proof obligation to the Z3 SMT solver, with a timeout in seconds.
Z3(t) == [backend |-> "Z3", timeout |-> t, tactic |-> NoTactic]

\* Dispatch a proof obligation to the SPASS prover, with a timeout in seconds.
SPASS(t) == [backend |-> "SPASS", timeout |-> t, tactic |-> NoTactic]

\* Dispatch a proof obligation to the LS4 temporal-logic prover, with a timeout in seconds.
LS4(t) == [backend |-> "LS4", timeout |-> t, tactic |-> NoTactic]

\* Invariance rule: a state predicate that holds in the initial state and is
\* preserved by every step is an invariant.
Invariance(f) == /\ f[0]
                  /\ \A i \in Nat : f[i+1]

\* Well-formedness rule: every action in a behavior is enabled at its own state,
\* so the behavior is a legal execution trace (no deadlock at any step).
WellFormed(b) == \A i \in Nat : b[i] # [backend |-> NoBackend, timeout |-> 0, tactic |-> NoTactic]

\* Strong fairness rule: a strongly fair action that is always enabled eventually fires.
StrongFair(f) == (\A i \in Nat : f[i]) ~> (\E i \in Nat : ~f[i])

\* Weak fairness rule: a weakly fair action that is always enabled eventually stops being enabled.
WeakFair(f) == (\A i \in Nat : f[i]) ~> (\E i \in Nat : ~f[i])

\* Step simulation rule: every action either advances to a strictly later state
\* or is already final, so a non-final behavior never stalls.
StepSim(b) == \A i \in Nat : (b[i] # [backend |-> NoBackend, timeout |-> 0, tactic |-> NoTactic])
                          => (b[i+1] # b[i])

\* The specification tracks a behavior (finite, growing sequence) of dispatched
\* proof obligations; dispatching is the only operation, which never fails.
\* Bump(i) appends the i-th proof step to a behavior that is currently shorter than i.
Bump(i) == IF Len(b) < i THEN b' = Append(b, [backend |-> "none", timeout |-> 0, tactic |-> NoTactic])
                        ELSE UNCHANGED b

\* An accepted dispatch replaces the next Proof step with a backend directive.
Accept(step == [backend |-> "none", timeout |-> 0, tactic |-> NoTactic]
    /\ Len(b) < 2
    /\ b' = Append(b, step)

Spec == /\ Len(b) = 0
        /\ \A i \in {1, 2} : Bump(i)
        /\ Accept(Zenon(1))

\* A well-formed behavior that is not already at the last step always has a
\* next step available -- this is the property the proof system relies on.
LiveStep == \A i \in Nat : (i < Len(b) /\ b[i+1] # [backend |-> NoBackend, timeout |-> 0, tactic |-> NoTactic])
                                   ~> (i+1 < Len(b))

(* Every set that contains every possible value must equal the universal set. *)
Extensionality == \A X \in SUBSET Nat : (\A x \in Nat : x \in X) => (X = Nat)

(* No set contains every possible value. *)
NoUniversalSet == ~(\A x \in Nat : x \in Nat)

\* Invariance and fairness rules are reserved names (from Lamport's TLA+ book);
\* they are declared here so later modules cannot silently reuse them.
InitDeclared == /\ Init == UNCHANGED
                 /\ Spec = Spec

====