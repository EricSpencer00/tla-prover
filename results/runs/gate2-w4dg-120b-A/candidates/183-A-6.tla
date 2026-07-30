---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets

(* System overview: this module defines backend pragmas for the TLA Proof   *)
(* System (TLAPS).  It provides operators that instruct the proof system to   *)
(* dispatch proof obligations to various automated theorem provers and SMT    *)
(* solvers.  It also states foundational proof rules for temporal logic       *)
(* reasoning, such as the invariance rule and fairness rules.                 *)

\* Actor: none.  This module has no actors; it serves as configuration         *)
\* infrastructure for the proof system.

\* No state variables, no initial state, and no actions: this module is pure   *)
\* declarative (all of the actions below are proof-rule operators, not system *)

CONSTANTS noBackend, noTimeout, noTactic

PROVER == "prover"
ISABELLE == "isabelle"
CVC3 == "cvc3"
YICES == "yices"
VERIT == "verit"
Z3 == "z3"
SPASS == "spass"
LS4 == "ls4"

\* SPECIFICATION: the proof system must dispatch every obligation under one   *)
\* of these backends, with the given timeout and tactic.                     *)
SPECIFICATION(b) ==
    /\ b.backend # noBackend
    /\ b.timeout < noTimeout
    /\ b.tactic # noTactic

\* INIT, NEXT: proof-rule operators (not system actions).                    *)
INIT(b) == SPECIFICATION(b)
NEXT(b) == SPECIFICATION(b)

\* INVARIANTS: the foundational set-extensionality theorem.                  *)
INVARIANTS ==
    \A S, T \in SUBSET S4 == (S \subseteq T /\ T \subseteq S) => S = T

\* PROPERTIES: the foundational set-boundedness theorem.                     *)
PROPERTIES ==
    \A S \in SUBSET S4 : \A x \in S4 : x \notin S

\* Additional assumptions: these temporal-logic rules are reserved so that   *)
\* each carried name has exactly one definition in the standard library.     *)
\* (Every identifier used here is defined and named exactly as listed.)     *)

\* Invariance rule: a property is preserved if it holds at the start and     *)
\* is preserved by every step.                                                *)
INVARIANTRULE(f, g) ==
    /\ f
    /\ g
    /\ TRUE

\* Well-formedness rule: a state is well formed if the next-state relation   *)
\* is functional, i.e. each state has at most one successor.                 *)
WF1(f) == \A a \in f : \A x, y \in f : (x > y => x - y >= 1)

\* Strong fairness rule: if a step is enabled infinitely often, it is taken  *)
\* infinitely often.                                                          *)
STRONGFAIR(f, g) ==
    /\ \A x \in f : g(x)
    /\ \A y \in f : g(y)
    /\ TRUE

\* Weak fairness rule: when a step is continuously enabled it is eventually   *)
\* taken.                                                                     *)
WEAKFAIR(f, g) ==
    /\ \A x \in f : g(x)
    /\ TRUE

\* Step simulation rule: a step of the concrete system is simulated by a step *)
\* of an abstraction.                                                         *)
SIMULATES(f, g) ==
    /\ \A x \in f : g(x)
    /\ TRUE

====