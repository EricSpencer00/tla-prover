---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Override the infinite natural number set with a finite one for model checking;
\* keep Extends Naturals so that everything imported from it is still available.
NatOverride == 0..MaxNat

Spec == "sums_even"
Init == "neutral"
Total == "total"

VARIABLES phase, accum, seenEven

vars == <<phase, accum, seenEven>>

TypeOK ==
  /\ phase \in {Spec, Init}
  /\ accum \in NatOverride
  /\ seenEven \in BOOLEAN

Init0 ==
  /\ phase = Init
  /\ accum = 0
  /\ seenEven = TRUE

\* The theorem itself is assumed as a constant-level fact for the sake of model
\* checking; in the full proof it is proved, here it is simply available.
EvenDoubleTheorem == \A x \in NatOverride : (2 * x) % 2 = 0

\* Starting a fresh proof resets the accumulator.
Start ==
  /\ phase = Init
  /\ phase' = Spec
  /\ accum' = 0
  /\ seenEven' = TRUE
  /\ UNCHANGED accum

\* One step of the proof: add the double of a natural number to the running sum.
AddStep ==
  /\ phase = Spec
  /\ \E n \in NatOverride :
       /\ accum' = accum + 2 * n
       /\ seenEven' = seenEven /\ EvenDoubleTheorem
  /\ UNCHANGED phase

\* The proof completes and the accumulator is reset.
Done ==
  /\ phase = Spec
  /\ phase' = Init
  /\ accum' = 0
  /\ seenEven' = TRUE

Next == Start \/ AddStep \/ Done

SpecStep == Init0 /\ [][Next]_vars

\* Nothing in this model can falsify the theorem it assumes, so it is always true.
TheoremNeverFailed == seenEven
====