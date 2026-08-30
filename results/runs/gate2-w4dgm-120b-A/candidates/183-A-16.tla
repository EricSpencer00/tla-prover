---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

VARIABLES proofObligations, assignedProver, timeoutCount, appliedTactics

vars == <<proofObligations, assignedProver, timeoutCount, appliedTactics>>

Provers == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

TypeOK ==
  /\ proofObligations \subseteq Provers
  /\ assignedProver \in Provers
  /\ timeoutCount \in Nat
  /\ appliedTactics \subseteq [obligation : Provers, prover : Provers]

Init ==
  /\ proofObligations = Provers
  /\ assignedProver = Z3
  /\ timeoutCount = 0
  /\ appliedTactics = {}

Assign(newP) ==
  /\ assignedProver' = newP
  /\ UNCHANGED <<proofObligations, timeoutCount, appliedTactics>>

Attempt(ob, prov) ==
  /\ ob \in proofObligations
  /\ prov = assignedProver
  /\ timeoutCount < 2
  /\ proofObligations' = proofObligations \ {ob}
  /\ appliedTactics' = appliedTactics \cup {[obligation |-> ob, prover |-> prov]}
  /\ UNCHANGED <<assignedProver, timeoutCount>>

Expire ==
  /\ timeoutCount < 2
  /\ timeoutCount' = timeoutCount + 1
  /\ UNCHANGED <<proofObligations, assignedProver, appliedTactics>>

Return(ob) ==
  /\ ob \notin proofObligations
  /\ proofObligations' = proofObligations \cup {ob}
  /\ appliedTactics' = { t \in appliedTactics : t.obligation # ob }
  /\ UNCHANGED <<assignedProver, timeoutCount>>

Next ==
  \/ \E p \in Provers : Assign(p)
  \/ \E ob \in Provers, prov \in Provers : Attempt(ob, prov)
  \/ Expire
  \/ \E ob \in Provers : Return(ob)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Expire)

ExtensionalSetsEqual ==
  \A a, b \in SUBSET Provers : (\A x \in Provers : (x \in a) <=> (x \in b)) => a = b

NoSetContainsAllValues == \A a \in SUBSET Provers : a # Provers

SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == ExtensionalSetsEqual
PROPERTIES == NoSetContainsAllValues
====