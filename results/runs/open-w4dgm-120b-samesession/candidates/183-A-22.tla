---- MODULE TLAPS ----
EXTENDS Naturals, Sequences

\* Backend provers for TLAPS: these operators command the proof system to
\* invoke the named prover on the current obligation, and carry the exact
\* parameter shape that each prover's driver expects.
Dispatch == "Dispatch"

\* The "prove with Zenon" operator takes an explicit timeout, since Zenon's
\* search can be cut off if it runs past the deadline.
Zenon(timeout) == [op |-> "zenon", args |-> timeout, kind |-> Dispatch]

\* Isabelle needs a proof method, so the method name flows in the second
\* argument slot rather than a timeout.
Isabelle(method) == [op |-> "isabelle", args |-> method, kind |-> Dispatch]

\* CVC3, Yices, veriT, Z3, SPASS, and LS4 all run as fire-and-forget
\* solvers: no timeout, no method, just the name of the solver.
CVC3 == [op |-> "cvc3", args |-> {}, kind |-> Dispatch]
Yices == [op |-> "yices", args |-> {}, kind |-> Dispatch]
VeriT == [op |-> "verit", args |-> {}, kind |-> Dispatch]
Z3 == [op |-> "z3", args |-> {}, kind |-> Dispatch]
SPASS == [op |-> "spass", args |-> {}, kind |-> Dispatch]
LS4 == [op |-> "ls4", args |-> {}, kind |-> Dispatch]

Enqueue(c) == [op |-> "enqueue", args |-> c, kind |-> "Enqueue"]

\* The dispatch queue is a sequence (a bounded worklist) with a fixed
\* ceiling; the cell at the head is the next obligation the proof engine
\* will hand to whichever backend is currently fastest.
QueueDepth == 2
VARIABLES queue, covered, called, done

TypeOK ==
  /\ queue \in Seq([op: {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"},
                   args: UNION {Nat, {}}])
  /\ Len(queue) <= QueueDepth
  /\ covered \subseteq {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}
  /\ called \subseteq {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}
  /\ done \subseteq {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

Init ==
  /\ queue = << >>
  /\ covered = {}
  /\ called = {}
  /\ done = {}

Enqueue(c) == Enqueue(c)

Enqueue(c) =
  /\ Len(queue) < QueueDepth
  /\ queue' = Append(queue, c)
  /\ UNCHANGED <<covered, called, done>>

\* Dispatch is the single critical section: exactly one prover runs for a
\* given obligation, and the head of the queue is always the next one to
\* be assigned, so no obligation is ever dispatched twice.
Dispatch ==
  /\ Len(queue) > 0
  /\ LET h == Head(queue) IN
       /\ h.op \notin called
       /\ called' = called \cup {h.op}
       /\ queue' = Tail(queue)
  /\ UNCHANGED <<covered, done>>

\* Backends report their result asynchronously in any order. Each result
\* lands exactly once, and landing removes the prover from the called set
\* so it can pick up a new obligation later.
Report(s) ==
  /\ s \in called
  /\ s \notin done
  /\ done' = done \cup {s}
  /\ called' = called \ {s}
  /\ UNCHANGED <<queue, covered>>

Idle == UNCHANGED <<queue, covered, called, done>>

Next ==
  \/ \E c \in {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}: Enqueue(c)
  \/ Dispatch
  \/ \E s \in {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}: Report(s)
  \/ Idle

Spec == Init /\ [][Next]_<<queue, covered, called, done>>

\* A prover is covered by the dispatcher exactly when it has produced a
\* result, and a result only ever lands for a prover that was actually
\* dispatched, so no prover's result is silently invented or lost.
CoverageMatchesDispatch ==
  /\ covered = done
  /\ done \subseteq called

\* Congestion-freedom: the bounded queue never backs up forever; every
\* enqueued obligation eventually leaves the queue.
QueueDrains == (Len(queue) > 0) ~> (Len(queue) = 0)

\* The full set of reserved rule names from Lamport's TLA+ paper; these
\* are all invariant properties so their names stay reserved even though
\* none is separately proved in this configuration module.
SetExtensionality ==
  \A S, T \in SUBSET Nat: (\A x \in Nat: (x \in S) <=> (x \in T)) => S = T

NoSetIsUniversal ==
  \A S \in SUBSET Nat: S # Nat
====