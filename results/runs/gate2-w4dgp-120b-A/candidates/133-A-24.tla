---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

(* A model-checking configuration module for the parallel reachability    *)
(* algorithm.  This module plugs in concrete, finite choices for the     *)
(* graph structure and overrides the unbounded sequence type with a      *)
(* bounded version, so the state space stays finite.                     *)
(* Inherited names:  marked, frontier, pc, sel, succs, Init, Next,       *)
(*                  Inv, Refines                                     *)

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working", "done"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> Seq(Nodes)]

Init == Init

Next == Next

Spec == Spec

Inv == Inv

Refines == Refines

(* The graph structure used in the sequential module was: every node
   has exactly two successors, drawn from a fixed small set so that the
   reachable subgraph is fully covered.  Here that fixed set is simply
   the whole node set, which is finite and small.  The link is wired
   through the ConnectedToSomeButNotAll name the .cfg substitutes in. *)
\* Override: ConnectedToSomeButNotAll is the operator the .cfg substitutes for Succ.
ConnectedToSomeButNotAll(n) == {m \in Nodes : m # n}

(* The .cfg replaces the built-in unbounded Seq operator with LimitedSeq,
   which caps per-process histories at the number of nodes, so no worker's
   successor log can grow without bound.  EXTENDS Sequences stays in force
   because the shape is still that of a sequence; only the length bound is
   added here. *)
LimitedSeq(S) == CHOOSE s \in Seq(S) : Len(s) <= Cardinality(Nodes)

====