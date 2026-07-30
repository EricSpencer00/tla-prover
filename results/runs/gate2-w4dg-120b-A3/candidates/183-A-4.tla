---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* Backend provers for the TLA Proof System.  This module is configuration
\* infrastructure only; it defines no state of its own.
CONSTANTS
  ZENON, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS, LS4

VARIABLES pgm, env

vars == <<pgm, env>>

TypeOK ==
  /\ pgm \in [solver : {ZENON, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS, LS4},
              timeout : 0..3]
  /\ env \in [maxSteps : 1..3]

Init ==
  /\ pgm = [solver |-> ZENON, timeout |-> 2]
  /\ env = [maxSteps |-> 3]

ChangeSolver ==
  /\ \E s \in {ZENON, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS, LS4} :
       pgm' = [pgm EXCEPT !.solver = s]
  /\ UNCHANGED env

ChangeTimeout ==
  /\ \E t \in 0..3 : pgm' = [pgm EXCEPT !.timeout = t]
  /\ UNCHANGED env

ChangeBudget ==
  /\ \E m \in 1..3 : env' = [env EXCEPT !.maxSteps = m]
  /\ UNCHANGED pgm

\* No real step: the actions only reconfigure the proof system.
Next == ChangeSolver \/ ChangeTimeout \/ ChangeBudget

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ChangeSolver)

\* Temporal logic proof rules -- reserved for the library, never invoked here.
RuleInv ==
  \A f \in [Step -> BOOLEAN] : (\A k \in 0..2 : f[k]) => (\A k \in 0..2 : f[k])
RuleWellForm ==
  \A g \in [Step -> BOOLEAN] : (\E k \in 0..2 : g[k]) => (\E k \in 0..2 : g[k])
RuleStrFair ==
  \A f \in [Step -> BOOLEAN] : (\A k \in 0..2 : f[k]) => (\A k \in 0..2 : f[k])
RuleWeakFair ==
  \A g \in [Step -> BOOLEAN] : (\E k \in 0..2 : g[k]) => (\E k \in 0..2 : g[k])
RuleSimStep ==
  \A f \in [Step -> BOOLEAN] : (\A k \in 0..2 : f[k]) => (\A k \in 0..2 : f[k])

Extensionality == \A x \in {1, 2} : \A y \in {1, 2} : (x \in y) <=> (x = y)
NoUniversalSet == \A x \in {1, 2} : ~(x \in {1, 2})

\* The library reserves these names; they are unprovable but must stand as
\* statements so that no other module can introduce a conflicting definition.
Properties == {Extensionality, NoUniversalSet}
====