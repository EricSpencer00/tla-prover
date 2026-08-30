---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS MaxVal, MaxLen

\* Set that a store instance has exclusive access to while it holds it.
VARIABLES lock, applied

vars == <<lock, applied>>

TypeOK ==
  /\ lock \in 0..MaxVal
  /\ applied \in 0..MaxLen

Init ==
  /\ lock = 0
  /\ applied = 0

\* Acquire the lock when it is free.
Acquire ==
  /\ lock = 0
  /\ \E v \in 1..MaxVal \ {lock} : lock' = v
  /\ applied' = applied

\* Apply one update, only while holding the lock.
Apply ==
  /\ lock # 0
  /\ applied < MaxLen
  /\ applied' = applied + 1
  /\ UNCHANGED lock

\* Release the lock.
Release ==
  /\ lock # 0
  /\ lock' = 0
  /\ UNCHANGED applied

Next ==
  \/ Acquire
  \/ Apply
  \/ Release

Spec == Init /\ [][Next]_vars

BoundedCreditCardUpdates ==
  /\ applied <= MaxLen
  /\ lock' # 0 => lock' \notin {lock, 0}

====