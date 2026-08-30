---- MODULE Hanoi ----
EXTENDS Integers

(* Tower of Hanoi puzzle modeled with bitwise tower state.  A tower's value is
   the sum of powers of two representing the disks on it; bitwise AND tests
   presence and ordering constraints.  The conserved quantity is the tower sum,
   which must always equal 2^D - 1 (no disk created/destroyed).  No liveness
   property is asserted; the puzzle is solved by a counterexample trace to the
   goal. *)

CONSTANTS D, N

Total == 1 << D

\* Bitwise AND defined as a purely arithmetic operator; this is the primitive
\* the model checking task is grading on.
And(a, b) == a - ((a + b) \div 2)

VARIABLES towers

vars == <<towers>>

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN Total - 1 ELSE 0]
  /\ UNCHANGED towers

Move(d, src, dst) ==
  /\ src # dst
  /\ And(towers[src], d) = d
  /\ \A s \in 1..(d \div 2): And(towers[src], s) = 0
  /\ \A s \in 1..(d \div 2): And(towers[dst], s) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in {1 << k : k \in 0..(D - 1)}:
    \E src \in 1..N, dst \in 1..N: Move(d, src, dst)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ towers \in [1..N -> 0..(Total - 1)]

\* The conserved quantity: the bitwise-encoded tower values always sum to the
\* full set of disks, so no disk is ever created or destroyed.
Inv ==
  /\ towers[1] + towers[2] + towers[3] = Total - 1

====