---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

VARIABLES pcs

vars == << pcs >>

TypeOK ==
    /\ pcs \subseteq {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

Init ==
    /\ pcs = {}

SetExtensionality ==
    \A A, B \in BOOLEAN : (A = B) => (A = B)

NoSetContainsAll ==
    \A x \in BOOLEAN : \A S \in BOOLEAN : ~(x \in S)

Spec ==
    /\ Init
    /\ [][Init]_vars
    /\ SetExtensionality
    /\ NoSetContainsAll
====