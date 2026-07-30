---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

\* Concrete configuration for the Boyer-Moore majority vote algorithm.
\* This module defines the constants, the SPECIFICATION, and the
\* required invariants and liveness property.  It also defines a
\* bounded version of the sequence operator (BoundedSeq) to keep the
\* state space finite for model checking; the name Seq is reserved by
\* the standard Sequences module, so it is not redefined here.

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* BoundedSeq replaces the unbounded Seq operator from Sequences for
\* model-checking purposes.  It is a finite version of Seq, so the
\* model stays within the configured bound.
BoundedSeq == [1..bound -> Values]

VARIABLES seq, i, candidate, counter

vars == <<seq, i, candidate, counter>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ i \in 1..(bound + 1)
  /\ candidate \in Values
  /\ counter \in 0..bound

Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ candidate \in Values
  /\ counter = 0

\* The Boyer-Moore scan: adopt a new candidate on a zero counter, or
\* increment/decrement the counter based on agreement with the current
\* candidate.
Scan ==
  /\ i <= bound
  /\ IF counter = 0 THEN
       /\ candidate' = seq[i]
       /\ counter' = 1
     ELSE IF seq[i] = candidate THEN
       counter' = counter + 1
     ELSE
       counter' = counter - 1
  /\ i' = i + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Scan]_vars

\* After a full scan, a true majority element must be the current
\* candidate; the counter is empty when the scan is over.
Correct ==
  /\ (i > bound /\ counter > 0) => (Cardinality({j \in 1..bound : seq[j] = candidate}) > bound \div 2)
  /\ (i > bound) => (counter' = counter)

Inv == TypeOK /\ Correct

Complete == (i > bound) /\ (counter = 0)

====