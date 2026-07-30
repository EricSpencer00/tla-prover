---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

SpecStage == [stage : {"init", "checking", "done"}]

VARIABLES
  dispatch, result, elapsed

vars == <<dispatch, result, elapsed>>

Dispatches == [to : {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}]

TypeOK ==
  /\ dispatch \in Dispatches
  /\ result \in {"none", "pass", "fail"}
  /\ elapsed \in 0..3

Init ==
  /\ dispatch = [to |-> Z3]
  /\ result = "none"
  /\ elapsed = 0

Send(prov) ==
  /\ dispatch' = [to |-> prov]
  /\ result' = "none"
  /\ elapsed' = 0

Resolve(res) ==
  /\ result = "none"
  /\ result' = res
  /\ UNCHANGED <<dispatch, elapsed>>

Tick ==
  /\ elapsed < 3
  /\ elapsed' = elapsed + 1
  /\ UNCHANGED <<dispatch, result>>

Next ==
  \/ \E prov \in {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4} : Send(prov)
  \/ \E res \in {"pass", "fail"} : Resolve(res)
  \/ Tick

Spec ==
  /\ Init
  /\ [][Next]_vars

SetExtensionality ==
  \A A, B \in SUBSET Nat : (A = B) <=> (\A x \in Nat : (x \in A) <=> (x \in B))

NoSetContainsAllVals ==
  \A A \in SUBSET Nat : \E x \in Nat : x \notin A

====