---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Z3Version, SPASSVersion

Spec == "set-theoretic"
Backend == "temporal"

ASSUME Spec \in {"set-theoretic", "temporal"}
ASSUME Z3Version \in Naturals
ASSUME SPASSVersion \in Naturals

RECURSIVE Tally(_, _)
Tally(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Tally(f, S \ {x})

\* Dispatch a proof obligation to a SAT/SMT solver with a timeout (default 1s):
\* the backend is the SMT solver, and the theory is the logic fragment.
DispatchSMT(obl, backend, theory) ==
  /\ backend \in {"yices", "z3", "cvc3"}
  /\ theory \in {"QF_UF", "QF_UFIDL", "QF_UFLRA"}
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>

\* Dispatch to an interactive theorem prover that runs a tactic package.
DispatchITP(obl, prover, config) ==
  /\ prover \in {"isabelle", "coq"}
  /\ config \in {"default", "intensive"}
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>

DispatchLS4(obl) ==
  /\ Spec = "temporal"
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>

\* Zenon's brute-force backtracking is disabled by default, but the prover
\* is still available for obligations that need it.
DispatchZenon(obl) ==
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>

DispatchSPASS(obl) ==
  /\ Spec = "temporal"
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>

\* Temporal logic proof rules from Lamport's 'The Temporal Logic of Actions':
\* these are basic skeletons; the proof system fills in the details.
InvRule ==
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>
  /\ \E p \in {"P", "Q", "R"} : TRUE

WFRule ==
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>
  /\ \E s \in {"s1", "s2"} : TRUE

SFRule ==
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>
  /\ \E g \in {"g1", "g2"} : TRUE

StepRule ==
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>
  /\ \E a \in {"a1", "a2"} : TRUE

\* The speciated-theory arithmetic rules remaining after the SMT dispatch:
\* they are the arithmetic skeletons the SMT solvers flesh out.
ArithRule ==
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>
  /\ \E e \in {"e1", "e2"} : TRUE

SimpRule ==
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>
  /\ \E r \in {"r1", "r2"} : TRUE

\* Foundational set lemmas, always available to any proof branch.
ExtLemma ==
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>
  /\ \A a, b \in (1..2) : a \in {1, 2} /\ b \in {1, 2} => (a = b <=> \A x \in {1, 2} : (x = a) <=> (x = b))

UndefLemma ==
  /\ UNCHANGED <<Spec, Z3Version, SPASSVersion>>
  /\ \A s \in (1..2) : ~(\A x \in (1..2) : x \in s)

Next ==
  \/ \E obl \in {"obl1", "obl2"} : DispatchSMT(obl, "yices", "QF_UF")
  \/ \E obl \in {"obl1", "obl2"} : DispatchSMT(obl, "z3", "QF_UF")
  \/ \E obl \in {"obl1", "obl2"} : DispatchSMT(obl, "cvc3", "QF_UF")
  \/ \E obl \in {"obl1", "obl2"} : DispatchITP(obl, "isabelle", "default")
  \/ \E obl \in {"obl1", "obl2"} : DispatchITP(obl, "coq", "intensive")
  \/ \E obl \in {"obl1", "obl2"} : DispatchZenon(obl)
  \/ \E obl \in {"obl1", "obl2"} : DispatchLS4(obl)
  \/ \E obl \in {"obl1", "obl2"} : DispatchSPASS(obl)
  \/ InvRule
  \/ WFRule
  \/ SFRule
  \/ StepRule
  \/ ArithRule
  \/ SimpRule
  \/ ExtLemma
  \/ UndefLemma

Spec == Next

Init == UNCHANGED <<Spec, Z3Version, SPASSVersion>>

Properties == {ExtLemma, UndefLemma}

====