---- MODULE TLAPS ----
EXTENDS Naturals

(* Backends for the TLA+ Proof System.  The operators below are not           *)
(* executed as ordinary TLA+ actions; they are directives to the proof          *)
(* system's dispatcher, used when TLAPS expands a proof step.  They are also    *)
(* the symbols the configuration file refers to, so this module must define    *)
(* each of them exactly once.                                                  *)

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4

Directives == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4}

SpecVersion == 2
ConfigHash == "a1b2c3d4"

\* These are the backend-invocation directives the proof system understands,
\* each paired with the name of the prover it talks to.
Dispatchers == [Zenon |-> "Zenon", Isabelle |-> "Isabelle", CVC3 |-> "CVC3",
                 Yices |-> "Yices", VeriT |-> "veriT", Z3 |-> "Z3",
                 Spass |-> "SPASS", LS4 |-> "LS4"]

\* A directive may be issued with no timeout, or with a deadline on how long
\* the prover may take to answer.  The timeout budget is a natural number.
TimeoutBudget == 2

NoDirective == "no_directive"

VARIABLES pending, dispatched, completed, dead

vars == <<pending, dispatched, completed, dead>>

TypeOK ==
  /\ pending \in Directives \cup {NoDirective}
  /\ dispatched \in [Directives -> BOOLEAN]
  /\ completed \in [Directives -> BOOLEAN]
  /\ dead \in BOOLEAN

Init ==
  /\ pending = NoDirective
  /\ dispatched = [d \in Directives |-> FALSE]
  /\ completed = [d \in Directives |-> FALSE]
  /\ dead = FALSE

\* A backend directive becomes the next thing the dispatcher will send to
\* its prover -- provided nothing is already queued and the system has not
\* crashed.  It can be paired with a timeout budget when it is emitted.
Emit(d) ==
  /\ pending = NoDirective
  /\ ~ dead
  /\ pending' = d
  /\ UNCHANGED <<dispatched, completed, dead>>

\* Dispatching is what the proof system counts as work done: the backend
\* is told what to try and the engine marks the directive sent.
Dispatch(t) ==
  /\ pending # NoDirective
  /\ ~ dispatched[pending]
  /\ dispatched' = [dispatched EXCEPT ![pending] = TRUE]
  /\ UNCHANGED <<pending, completed, dead>>

\* Completion is the prover answering, which is what the engine may wait
\* on before moving on to the next proof step.
Complete ==
  /\ pending # NoDirective
  /\ dispatched[pending]
  /\ ~ completed[pending]
  /\ completed' = [completed EXCEPT ![pending] = TRUE]
  /\ UNCHANGED <<pending, dispatched, dead>>

\* Backends can always be sent another directive once their prior one has
\* been answered; completion clears the queue slot.
Recycle ==
  /\ pending # NoDirective
  /\ completed[pending]
  /\ pending' = NoDirective
  /\ dispatched' = [dispatched EXCEPT ![pending] = FALSE]
  /\ completed' = [completed EXCEPT ![pending] = FALSE]
  /\ UNCHANGED dead

\* The dispatcher may crash silently at any moment, which freezes the
\* queue and any answer already en route forever.
Crash ==
  /\ ~ dead
  /\ dead' = TRUE
  /\ UNCHANGED <<pending, dispatched, completed>>

AllAnswersReturned == \A d \in Directives : completed[d]

Next ==
  \/ \E d \in Directives : Emit(d)
  \/ \E t \in [directions : Directives, budget : 0 .. TimeoutBudget] : Dispatch(t)
  \/ Complete
  \/ Recycle
  \/ Crash

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Complete)
  /\ WF_vars(Recycle)

\* Two foundational theorems about sets, restated here so their names are
\* reserved and cannot be claimed by a later module's definition.
Extensionality ==
  \A A, B \in SUBSET Directives : (\A x \in Directives : (x \in A) <=> (x \in B)) => (A = B)

NoUniversalSet ==
  \A x \in Directives : x \notin Directives

\* Temporal-logic proof rules from Lamport's TLA book: these are included
\* as reserved symbols, not as steps the system performs.
TemporalRules ==
  /\ \A p \in SUBSET Directives : (p = {}) \/ (\E d \in Directives : p = {d})
  /\ \A p \in SUBSET Directives : \A q \in SUBSET Directives : (p \cap q = {}) /\ (p \cup q = Directives) => (p = Directives \ q)
  /\ \A p \in SUBSET Directives : \A q \in SUBSET Directives : (p \cup q = Directives) => (\A d \in Directives : (d \in p) \/ (d \in q))
  /\ \A p \in SUBSET Directives : (p # {}) => (\E d \in Directives : d \in p) = TRUE
  /\ \A p \in SUBSET Directives : (p # {}) => (\A d \in Directives : (d \in p) <=> (p = {d}))
  /\ \A p \in SUBSET Directives : (\E d \in Directives : (d \in p)) => (p # {})
  /\ \A p \in SUBSET Directives : (\A d \in Directives : (d \in p)) <=> (p = Directives)

\* Nothing is ever left pending forever: every directive that is queued is
\* eventually either sent to its prover or superseded by the system's own
\* progress (a completed answer, or the crash that freezes the backends).
Termination == <>(AllAnswersReturned \/ dead)

====