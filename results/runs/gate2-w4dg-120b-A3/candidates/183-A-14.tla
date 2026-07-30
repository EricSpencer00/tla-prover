---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4,
          invRule, wfRule, sfRule, wsimRule

Spec == <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, invRule, wfRule, sfRule, wsimRule>>

Init ==
  /\ Zenon = 0
  /\ Isabelle = 0
  /\ CVC3 = 0
  /\ Yices = 0
  /\ veriT = 0
  /\ Z3 = 0
  /\ SPASS = 0
  /\ LS4 = 0
  /\ invRule = 0
  /\ wfRule = 0
  /\ sfRule = 0
  /\ wsimRule = 0

Next ==
  /\ Zenon < 2
  /\ Zenon' = Zenon + 1
  /\ UNCHANGED <<Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, invRule, wfRule, sfRule, wsimRule>>
  \/ Isabelle < 2
  /\ Isabelle' = Isabelle + 1
  /\ UNCHANGED <<Zenon, CVC3, Yices, veriT, Z3, SPASS, LS4, invRule, wfRule, sfRule, wsimRule>>
  \/ CVC3 < 2
  /\ CVC3' = CVC3 + 1
  /\ UNCHANGED <<Zenon, Isabelle, Yices, veriT, Z3, SPASS, LS4, invRule, wfRule, sfRule, wsimRule>>
  \/ Yices < 2
  /\ Yices' = Yices + 1
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, veriT, Z3, SPASS, LS4, invRule, wfRule, sfRule, wsimRule>>
  \/ veriT < 2
  /\ veriT' = veriT + 1
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, Z3, SPASS, LS4, invRule, wfRule, sfRule, wsimRule>>
  \/ Z3 < 2
  /\ Z3' = Z3 + 1
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, veriT, SPASS, LS4, invRule, wfRule, sfRule, wsimRule>>
  \/ SPASS < 2
  /\ SPASS' = SPASS + 1
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, LS4, invRule, wfRule, sfRule, wsimRule>>
  \/ LS4 < 2
  /\ LS4' = LS4 + 1
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, invRule, wfRule, sfRule, wsimRule>>
  \/ invRule < 2
  /\ invRule' = invRule + 1
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, wfRule, sfRule, wsimRule>>
  \/ wfRule < 2
  /\ wfRule' = wfRule + 1
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, invRule, sfRule, wsimRule>>
  \/ sfRule < 2
  /\ sfRule' = sfRule + 1
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, invRule, wfRule, wsimRule>>
  \/ wsimRule < 2
  /\ wsimRule' = wsimRule + 1
  /\ UNCHANGED <<Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, invRule, wfRule, sfRule>>

Specification == Spec

Invariants == { invRule }

Properties ==
  { \A A, B \in SUBSET Nat : (A = B) <=> (\A x \in A : x \in B /\ \A x \in B : x \in A)
  , \A x \in Nat : x \notin { y \in Nat : TRUE }
  }

====