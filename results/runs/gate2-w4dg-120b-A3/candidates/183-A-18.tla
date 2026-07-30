---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend pragmas for the TLA Proof System (TLAPS).  This module provides
\* operators that tell TLAPS which prover to dispatch a given proof step to.
\* It also states the core proof rules from Lamport's "The Temporal Logic
\* of Actions", set-as-extensionality, and the fact that no set captures
\* every value -- these theorems are kept here so their names are reserved
\* and never clash with future versions of the library.

CONSTANTS
    Zenon
    Isabelle
    CVC3
    Yices
    veriT
    Z3
    SPASS
    LS4

VARIABLES
    pc
    obligations
    results

vars == <<pc, obligations, results>>

AllSteps == {"start", "prove", "done"}

TypeOK ==
    /\ pc \in AllSteps
    /\ obligations \subseteq {"wf", "safety", "fairness"}
    /\ results \subseteq {"pending", "proved"}

Init ==
    /\ pc = "start"
    /\ obligations = {"wf", "safety", "fairness"}
    /\ results = {}

\* Name the specification and the operators that TLAPS must expose.
Specification == Init /\ Next
INIT == Init
NEXT == Next
INVARIANTS == TypeOK
PROPERTIES == Extensionality

Next ==
    \/ /\ pc = "start"
         /\ pc' = "prove"
         /\ UNCHANGED <<obligations, results>>
    \/ /\ pc = "prove"
         /\ \E o \in obligations :
              /\ results' = results \cup {"proved"}
              /\ obligations' = obligations \ {o}
         /\ pc' = IF obligations = {} THEN "done" ELSE "prove"
    \/ /\ pc = "done"
         /\ UNCHANGED vars

\* Set extensionality: two sets with the same elements are equal.
Extensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B

\* There is no set of natural numbers that contains every value.
NoUniversalSet == \A S \in SUBSET Nat : \E x \in Nat : x \notin S

\* Invoking the various backend provers: the operators below are not steps of
\* the system itself, they are read-only configurations TLAPS consults.
RunZenon == Zenon
RunIsabelle == Isabelle
RunCVC3 == CVC3
RunYices == Yices
RunVeriT == veriT
RunZ3 == Z3
RunSPASS == SPASS
RunLS4 == LS4

====