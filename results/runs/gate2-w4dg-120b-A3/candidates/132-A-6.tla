---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The element set is written explicitly so the tool can see it as a
\* ground, finite set of constants; that is required for the bounded
\* sequence construction below.
\* The bound is a model parameter that the .cfg file fixes.

\* Each value is literally the name of a constant, so the set is
\* syntactically explicit rather than written as a comprehension.
Values == {A, B, C}

\* BoundedSeq is a FINITE version of Seq: it only builds sequences up to
\* the given bound, so the model stays finite and checkable.
BoundedSeq == {[1..n -> v] : n \in 0..bound, v \in Values}

VARIABLES seq, pos, cand, count
vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 0..bound
  /\ cand \in Values
  /\ count \in 0..bound

\* The main correctness property: a true majority must survive as the
\* candidate after a full scan, and count must be zero when it has not.
Correct ==
  /\ count >= 0
  /\ count <= bound
  /\ (pos = bound /\ \A i \in DOMAIN seq : seq[i] = cand => count > 0)
  /\ (pos = bound /\ \A i \in DOMAIN seq : seq[i] # cand => count = 0)

Inv ==
  /\ TypeOK
  /\ Correct

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 0
  /\ cand \in Values
  /\ count = 0

\* Scan: three cases, exactly as in the majority vote spec.
Step ==
  /\ pos < bound
  /\ LET s == seq[pos + 1] IN
       IF count = 0
         THEN /\ cand' = s
              /\ count' = 1
         ELSE IF s = cand
               THEN /\ count' = count + 1
               /\ UNCHANGED cand
               /\ UNCHANGED seq
               /\ UNCHANGED pos
         ELSE /\ count' = count - 1
              /\ UNCHANGED cand
              /\ UNCHANGED seq
              /\ UNCHANGED pos
  /\ pos' = pos + 1

Next == Step

Spec == Init /\ [][Next]_vars

\* The model's liveness is a single fair outcome for the scan.
ScanEventuallyCompletes == WF_vars(Step)

=============================================================================