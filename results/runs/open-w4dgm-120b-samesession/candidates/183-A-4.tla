---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

(* Backend provers: these are the provers TLAPS may dispatch to. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

(* Temporal logic proof rules: reserved names, never to be overloaded. *)
CONSTANTS Invariance, FormWellFormed, NoStuttering, FairStep, FairWeak

\* Set extensionality: two sets with the same elements are equal.
Extensionality ==
    \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B

\* No set contains every possible value; the universe is never captured.
NotUniversal ==
    \A A \in SUBSET Nat : (\A x \in Nat : TRUE) => (\E x \in Nat : x \notin A)

(* The module's public contract: the two theorems and the constant set. *)
SPECIFICATION == Extensionality
INVARIANTS == {NotUniversal}
PROPERTIES == {Extensionality, NotUniversal}
====