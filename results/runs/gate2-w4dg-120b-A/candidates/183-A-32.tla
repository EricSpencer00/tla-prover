---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Core proof rules imported from the standard library so that their names are
\* reserved here too, preventing future naming clashes.
EXTENDS TLA2TemporalLogic

VARIABLES clock, proofLog

vars == <<clock, proofLog>>

\* Proof steps are dispatched to backend provers; the clock models bounded
\* time, and the log records which prover was used for each step.
Steps == [kind : {"check", "simp"}, target : {"Zenon", "Isabelle", "CVC3",
                                            "Yices", "VeriT", "Z3", "SPASS", "LS4"}]

TypeOK ==
  /\ clock \in 0..2
  /\ proofLog \subseteq Steps

Init ==
  /\ clock = 0
  /\ proofLog = {}

\* A step is dispatched to a backend prover and the clock advances.
Dispatch ==
  /\ \E s \in Steps :
       /\ proofLog' = proofLog \cup {s}
       /\ clock' = (clock + 1) % 3
  /\ UNCHANGED <<>>

Spec ==
  /\ Init
  /\ [][Dispatch]_vars

\* Foundational invariance theorem: two sets with the same elements are equal.
Extensionality ==
  \A x \in SUBSET {0, 1} :
    \A y \in SUBSET {0, 1} : (x = y) <=> (\A z \in {0, 1} : (z \in x <=> z \in y))

\* No set contains every possible value in the domain.
BoundedUniverse ==
  \A x \in SUBSET {0, 1} : \E y \in {0, 1} : y \notin x

====