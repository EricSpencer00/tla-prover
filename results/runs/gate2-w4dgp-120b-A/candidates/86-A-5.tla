---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS SetTheory, Isabelle, Yices, CVC3, Z3

VARIABLES zenon, isabelle, cvc3, yices, spass, veriT, ls4

VARIABLE_STATUS == "queued" \/ "proving" \/ "proved"
TIMEOUT == 2

vars == <<zenon, isabelle, cvc3, yices, spass, veriT, ls4>>

Init ==
    /\ zenon = VARIABLE_STATUS
    /\ isabelle = VARIABLE_STATUS
    /\ cvc3 = VARIABLE_STATUS
    /\ yices = VARIABLE_STATUS
    /\ spass = VARIABLE_STATUS
    /\ veriT = VARIABLE_STATUS
    /\ ls4 = VARIABLE_STATUS

BeginProof ==
    /\ zenon = "queued"
    /\ isabelle = "queued"
    /\ cvc3 = "queued"
    /\ yices = "queued"
    /\ spass = "queued"
    /\ veriT = "queued"
    /\ ls4 = "queued"
    /\ zenon' = "proving"
    /\ isabelle' = "proving"
    /\ cvc3' = "proving"
    /\ yices' = "proving"
    /\ spass' = "proving"
    /\ veriT' = "proving"
    /\ ls4' = "proving"

FinishProof ==
    /\ zenon = "proving"
    /\ isabelle = "proving"
    /\ cvc3 = "proving"
    /\ yices = "proving"
    /\ spass = "proving"
    /\ veriT = "proving"
    /\ ls4 = "proving"
    /\ zenon' = "proved"
    /\ isabelle' = "proved"
    /\ cvc3' = "proved"
    /\ yices' = "proved"
    /\ spass' = "proved"
    /\ veriT' = "proved"
    /\ ls4' = "proved"

Timeout ==
    (zenon = "proving" /\ zenon' = "queued")
      \/ (isabelle = "proving" /\ isabelle' = "queued")
      \/ (cvc3 = "proving" /\ cvc3' = "queued")
      \/ (yices = "proving" /\ yices' = "queued")
      \/ (spass = "proving" /\ spass' = "queued")
      \/ (veriT = "proving" /\ veriT' = "queued")
      \/ (ls4 = "proving" /\ ls4' = "queued")
    /\ UNCHANGED <<zenon, isabelle, cvc3, yices, spass, veriT, ls4>>

Next == BeginProof \/ FinishProof \/ Timeout

Spec == Init /\ [][Next]_vars

NoEmptyDomain == \A S \in SUBSET SetTheory : (S # {}) => (\E x \in S : TRUE)
Extensionality ==
    \A A, B \in SUBSET SetTheory :
        (\A x \in SetTheory : (x \in A <=> x \in B)) => A = B

====