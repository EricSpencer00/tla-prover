---- MODULE TLAPS ----
EXTENDS Naturals

(* The TLA Proof System (TLAPS) backend pragmas that dispatch proof            *)
(* obligations to various theorem provers and SMT solvers.  Also declared are   *)
(* the fundamental temporal-logic proof rules from Lamport's TLA paper that   *)
(* this helper module reserves.                                                 *)

CONSTANTS zenon, isabelle, cvc3, yices, verit, z3, spass, ls4

VARIABLES dispatchCnt

vars == <<dispatchCnt>>

Init == dispatchCnt = 0

\* Backends are invoked by name and a timeout; the dispatch count is a
\* simple runtime statistic, not a correctness-critical value.
Dispatch(n, t) == dispatchCnt < 10 /\ dispatchCnt' = (dispatchCnt) + 1

SetExtensionality == \A a, b \in {{1, 2}, {1}, {2}} : (\A c \in a : c \in b) => (\A c \in b : c \in a) => a = b
NotEveryValue == \A a \in {{1, 2}, {1}, {2}} : \E c \in a : TRUE

Inv == SetExtensionality /\ NotEveryValue

Next == (\E n \in {zenon, isabelle, cvc3, yices, verit, z3, spass, ls4}, t \in {1, 2} : Dispatch(n, t))

TypeOK == dispatchCnt \in 0..10

Spec == Init /\ [][Next]_vars

====