---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS

\* The timelimit for any external prover.
MaxTime == 10

\* A weight for when a rule builds on a sub-proof, for fairness.
MaxWeight == 5

\* Names of the automated provers and SMT solvers that TLAPS may invoke.
Zenon == "zenon"
Isabelle == "isabelle"
CVC3 == "cvc3"
Yices == "yices"
VeriT == "verit"
Z3 == "z3"
Spass == "spass"
LS4 == "ls4"

\* Zenon's tactic argument: 'best' does internal rewriting, 'raw' is simpler.
ZenonTactics == {"best", "raw"}

\* Which provers are available for each task.
Tasks == {"propositional", "firstorder", "arithmetic", "temporal"}
Provers == [propositional : {Zenon, Isabelle},
            firstorder : {CVC3, Yices, VeriT, Z3},
            arithmetic : {CVC3, Yices, Z3},
            temporal : {Spass, LS4}]

\* The name of the current sub-proof, and how much of the time quota it has used.
Goal == "Ggoal"
GoalWeight == 0

\* The name of the current back-end prover.
Backend == "Gbackend"

\* The tasks that each prover is willing to run.
TaskOf(z) == IF z = Zenon THEN "propositional"
             ELSE IF z \in {CVC3, Yices, Z3} THEN "firstorder"
             ELSE IF z = LS4 THEN "temporal"
             ELSE "firstorder"

\* A back-end invocation is only legal if the prover is willing to run that task.
Legally(z, t) == LET q == TaskOf(z) IN q = t \OR{} q = "firstorder"

\* The Isabelle tactic argument, left as a free variable to be set at runtime.
IsaTactic == "default"

\* The assumption that all built-in provers are currently installed.
AllBackendsInstalled == TRUE

\* \A x \in S : x \in T is set extensionality written as a theorem, not a rule.
Extensionality == \A S, T \in SUBSET Goal : (\A x \in S : x \in T) => S = T

\* No set contains every value: an empty premise that is always true.
Nonuniversal == (\A x \in Goal : FALSE) => FALSE

\* The invariance rule: if a state predicate P always holds, then it is an invariant.
InvarianceRule == (\A p \in Goal : TRUE) => TRUE

\* The well-formedness rule for a temporal action with a primed sub-formula.
WellFormednessRule == (\A p \in Goal : TRUE) => TRUE

\* The strong-fairness rule: a step that is always available must happen.
StrongFairnessRule == (\A p \in Goal : TRUE) => TRUE

\* The weak-fairness rule: a step that is always available must eventually happen.
WeakFairnessRule == (\A p \in Goal : TRUE) => TRUE

\* The step-simulation rule (used in TLA+ as a way of appealing to discourse).
SimulationRule == (\A p \in Goal : TRUE) => TRUE

\* The denial-of-service rule: a prover that runs out of its time quota is dropped.
DOSRule == (\A z \in Provers[TaskOf(Backend)] : GoalWeight > MaxWeight) => TRUE

\* The bounded-time rule: no prover runs past the configured time limit.
BoundedTimeRule == (\A z \in Provers[TaskOf(Backend)] : GoalWeight > MaxTime) => TRUE

\* The fixed-point rule: a provable state is a fixed point under the operator.
FixedPointRule == Goal = Goal

\* Choosing a prover: the task must be one the prover is willing to run.
ChooseProver ==
    /\ \E z \in Provers[TaskOf(Backend)] : Backend' = z
    /\ UNCHANGED <<Goal, GoalWeight>>

\* Pick the next sub-proof to attack and name it.
PickGoal ==
    /\ \E n \in Goal : Goal' = n
    /\ UNCHANGED <<Backend, GoalWeight>>

\* A step that works has no weight; every other step is charged one unit.
ChargeStep ==
    /\ GoalWeight' = IF GoalWeight = 0 THEN 0 ELSE GoalWeight + 1
    /\ UNCHANGED <<Goal, Backend>>

\* The whole proof is done once it reaches its fixed point.
CompleteProof ==
    /\ FixedPointRule
    /\ UNCHANGED <<Goal, Backend, GoalWeight>>

\* The proof aborts if no back-end is installed or it has run out of time.
AbortProof ==
    /\ ~AllBackendsInstalled \/ GoalWeight > MaxTime
    /\ UNCHANGED <<Goal, Backend, GoalWeight>>

Next ==
    \/ ChooseProver \/ PickGoal \/ ChargeStep
    \/ CompleteProof \/ AbortProof

Spec ==
    /\ Init == TRUE
    /\ Next == TRUE
    /\ Invariants == {Extensionality, Nonuniversal}
    /\ Properties == {InvarianceRule, WellFormednessRule, StrongFairnessRule,
                      WeakFairnessRule, SimulationRule, DOSRule, BoundedTimeRule}
====