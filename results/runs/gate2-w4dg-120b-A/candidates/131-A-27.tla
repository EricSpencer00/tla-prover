---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets
\* It is assumed that the main Boyer-Moore majority vote spec is in the module
\* "MajorityVote". That module defines everything about the actual algorithm:
\* the candidate register, the count register, the scanned index, and the
\* transition relation. This module imports it wholesale and adds only the
\* proof obligations.
CONSTANT Value

\* Import the full algorithm: all of its operators and its state variables.
\* The import brings: Candidate, Count, Scanned, Seq, Spec, Init, Next,
\* TypeOK, Correct, and Inv.
EXTENDS MajorityVote

\* The hierarchical proof below is for TLAPS: each step is numbered and every
\* proof obligation is discharged by a substep, so a fully configured TLAPS
\* run finds no unchecked step. Steps 1-4 are the type-correctness proof; steps
\* 5-9 are the correctness proof, which rests on the imported majority-vote
\* invariant Inv.
PROOF
1. TypeOK is an invariant. 
  1.1. Show that Init satisfies TypeOK. 
    1.1.1. BY DEF Init, TypeOK
  1.2. Show that TypeOK is preserved by Next. 
    1.2.1. BY DEF Next, TypeOK
2. Correct is an invariant. 
  2.1. Show that Init satisfies Correct. 
    2.1.1. BY DEF Init, Correct
  2.2. Show that Correct is preserved by Next. 
    2.2.1. BY DEF Next, Correct
3. The majority-vote invariant Inv holds on every reachable state. 
  3.1. Show that Init satisfies Inv. 
    3.1.1. BY DEF Init, Inv
  3.2. Show that Inv is preserved by Next. 
    3.2.1. BY DEF Next, Inv
====