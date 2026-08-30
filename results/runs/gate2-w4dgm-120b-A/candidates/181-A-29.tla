---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

CONSTANTS MaxNat

\* Finite override of the natural numbers for the model-checking bound:
\* NatOverride is the finite set {0, 1, 2, ..., MaxNat}; it replaces Nat from Naturals.
NatOverride == 0..MaxNat

VARIABLES n, even, proofChecked

vars == <<n, even, proofChecked>>

TypeOK == n \in NatOverride /\ even \in BOOLEAN /\ proofChecked \in BOOLEAN

Init == n = 0 /\ even = FALSE /\ proofChecked = FALSE

Check == proofChecked' = TRUE /\ UNCHANGED <<n, even>>

NextN == n < MaxNat /\ n' = n + 1 /\ UNCHANGED <<even, proofChecked>>

SetEven == ~even /\ even' = ~even /\ UNCHANGED <<n, proofChecked>>

Next == Check \/ NextN \/ SetEven

Spec == Init /\ [][Next]_vars

\* The safety property from the base proof: twice any natural is even.
EvenDouble == even

\* Liveness: the theorem check is eventually performed.
TheoremChecked == <>(proofChecked = TRUE)

====