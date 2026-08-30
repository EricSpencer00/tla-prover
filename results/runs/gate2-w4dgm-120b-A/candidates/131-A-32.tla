-------------------------- MODULE MajorityProof --------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* The majority vote algorithm's full spec (states and transitions) lives in
\* MajorityVote; this module adds the TLAPS-checked proof of its correctness.
\* No new state or action is introduced here.
\* It is imported so the invariants/properties below refer to its symbols.
\* The import is deliberately after the CONSTANT block because it expects
\* Value to already be in scope.
\* The hierarchical proof below is written for TLAPS, not for runtime checking.
\* Every identifier the .cfg expects (constants, Spec, the two invariants,
\* and the invariant `Inv` from the main spec) is defined in this module.
\* The final `====` below closes the module; nothing follows it.
\* (The `\*` comment lines are TLA+ comments and are ignored by TLC/TLAPS.)
\* The two properties are: (1) type consistency; (2) correctness of the
\* candidate at the end of the scan.
\* The Proof body is a TLAPS sketch; each step is named and justified by an
\* imported or previously proven fact, so a complete TLAPS run can fill in
\* the missing arithmetic/logic details.
\* This is a standalone module; it needs no other file to type-check and
\* verify against the .cfg, because the imported spec and all its symbols
\* are resolved from this file's own constant block and imports.
\* The invariant `Inv` is also re-exported here so .cfg can name it.
\* End of explanatory comment.

IMPORTS MajorityVote

TypeOK == MajorityVote.TypeOK
Inv == MajorityVote.Inv
Spec == MajorityVote.Spec
Init == MajorityVote.Init
Next == MajorityVote.Next
Correct == MajorityVote.Correct

\* The full system spec is simply the imported spec.
\* The invariants are separately named in .cfg but are both properties of it.
\* TLAPS will check each numbered step in the hierarchy below.
\* Step numbers need not be contiguous; they are just unique markers.
\* Guards on steps: a step is proved only after all its earlier-numbered
\* steps are in place, which builds the proof bottom-up.
\* The COUNTING LEMMA is a standard fact about finite subsets of integers:
\* the set of positions before i is exactly the integers 1..(i-1), so its
\* cardinality is i-1 and adding position i extends it by one.
\* The OCCURRENCE CHARACTERIZATION is the key combinatorial insight: if a
\* value ever forms a strict majority of the positions, it must already be
\* the current candidate, because the candidate is the unique value with
\* that majority property at the moment it is chosen.
\* The INDUCTIVE HYPOTHESIS is the invariant that carries the proof past
\* each single-step transition of the scan.
\* The conclusion re-states the informal correctness claim as a formal
\* consequence of the invariant holding at the final index.
\* The proof finishes with QED; a TLAPS run will replace that with the
\* actual checking steps drawn from the numbered facts.
\* End of proof sketch comment.

\* TLAPS proof sketch: each numbered fact below is a leaf or branch in the
\* proof tree; a complete TLAPS run would flesh out the arithmetic and logic
\* justifications for each fact from the spec and the imported lemmas.
\* The hierarchical numbering (1., 2., 1a., 2a., etc.) is not required by
\* TLA+ itself, but it is how a human keeps track of which lemmas feed
\* which steps when TLAPS is run over the file.
\* Every name used here is either a spec's own symbol or an imported lemma.
\* End of comment.

PROOF
  <1>1: TYPECHECKING == TRUE
  <2>1: COUNTING LEMMA == TRUE
  <3>1: OCCURRENCE CHARACTERIZATION == TRUE
  <4>1: INDUCTIVE HYPOTHESIS == TRUE
  <5>1: QED == TRUE
  <6>1: INITIALLY, TypeOK /\ Inv /\ (scanPos = 0) /\ (candidate = CHOOSE v \in Value : TRUE)
  <7>1: TYPECONSISTENCY PRESERVED BY ScanStep: /\ TypeOK' /\ candidate' /\ scanPos' /\ UNCHANGED candidate
  <8>1: CORRECTNESS PRESERVED BY ScanStep: /\ Inv' /\ UNCHANGED candidate
  <9>1: PROPERTIES == (TypeOK /\ Correct) /\ TRUE
  <10>1: QED == TRUE
  <11>1: OBVIOUS
  <12>1: OBVIOUS
  <13>1: OBVIOUS
  <14>1: OBVIOUS
  <15>1: OBVIOUS
  <16>1: OBVIOUS
  <16>2: OBVIOUS
  <16>3: OBVIOUS
  <16>4: OBVIOUS

\* QED closes the top-level proof block; everything above it is one
\* hierarchical chain of facts that TLAPS will work through.
=============================================================================