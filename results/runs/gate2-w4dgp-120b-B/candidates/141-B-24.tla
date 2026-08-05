---- MODULE Reachable ----
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  The   *)
(* algorithm is due to Jayadev Misra.  It is, to my knowledge, a new       *)
(* variant of a fairly obvious breadth-first search for reachable nodes.   *)
(* I find this algorithm interesting because it is easier to implement     *)
(* using multiple processors than the obvious algorithm.  Module ParReach  *)
(* describes such an implementation.  You may want to read it after        *)
(* reading this module.                                                    *)
(*                                                                         *)
(* Module ReachableProofs contains a TLA+ proof of the algorithm's safety  *)
(* property--that is, partial correctness, which means that if the         *)
(* algorithm terminates then it produces the correct answer.  That proof   *)
(* has been checked by TLAPS, the TLA+ proof system.  The proof is based   *)
(* on ideas from an informal correctness proof by Misra.                   *)
(*                                                                         *)
(* In this module, reachability is expressed in terms of the operator      *)
(* ReachableFrom, where ReachableFrom(S) is the set of nodes reachable     *)
(* from the nodes in the set S of nodes.  This operator is defined in      *)
(* module Reachability.  That module describes a directed graph in terms   *)
(* of the constants Nodes and Succ, where Nodes is the set of nodes and    *)
(* Succ is a function with domain Nodes such that Succ[m] is the set of    *)
(* all nodes n such that there is an edge from m to n.  If you are not     *)
(* familiar with directed graphs, you should read at least the opening     *)
(* comments in module Reachability.                                        *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of notes reachable from Root.  The   *)
(* purpose of the algorithm is to compute Reachable.                       *)
(***************************************************************************)
Reachable == ReachableFrom({Root})
---------------------------------------------------------------------------
(***************************************************************************
The obvious algorithm for computing Reachable({Root}) is as follows.
There are two variables which, following Misra, we call `marked' and
vroot.  Each variable holds a set of nodes that are reachable from
Root.  Initially, marked = {} and vroot = {Root}.  While vroot is
non-empty, the obvious algorithm removed an arbitrary node v from
vroot, adds v to `marked', and adds to vroot all nodes in Succ[v] that
are not in `marked'.  The algorithm terminates when vroot is empty,
which will eventually be the case if Reachable({Root}) is a finite set.
When it terminates, `marked' equals Reachable({Root}).

In the obvious algorithm, `marked' and vroot are always disjoint sets of
nodes.  Misra's variant differs in that `marked' and vroot are not
necessarily disjoint.  While vroot is nonempty, it chooses an arbitrary
node and does the following:

  IF v is not in in `marked'
    THEN it performs the same action as the obvious algorithm except:
         (1) it doesn't remove v from vroot, and
         (2) it adds all nodes in Succ[v] to vroot, not just the ones 
             not in `marked'.
    ELSE it removes v from vroot
    
 Here is the algorithm's PlusCal code.

--fair algorithm Reachable {
  variables marked = {}, vroot = {Root};
  { a: while (vroot /= {})
        { with (v \in vroot)
           { if (v \notin marked)
                  { marked := marked \cup {v};
                    vroot  := vroot \cup Succ[v] }
             else { vroot := vroot \ {v} }
           }
        }
  }
}

***************************************************************************)

\* BEGIN TRANSLATION    Here is the TLA+ translation of the PlusCal code.
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == (* Global variables *)
        /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF vroot /= {}
           THEN /\ \E v \in vroot:
                     IF v \notin marked
                        THEN /\ marked' = (marked \cup {v})
                             /\ vroot' = (vroot \cup Succ[v])
                        ELSE /\ vroot' = vroot \ {v}
                             /\ UNCHANGED marked
                \/ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << marked, vroot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
----------------------------------------------------------------------------
(***************************************************************************)
(* Partial correctness is based on the invariance of the following four    *)
(* state predicates.  I have sketched very informal proofs of their        *)
(* invariance, as well of proofs of the the two theorems that assert       *)
(* correctness of the algorithm.  The module ReachableProofs contains      *)
(* rigorous, TLAPS checked TLA+ proofs of all except the last theorem.     *)
(* The last theorem asserts termination, which is a liveness property, and *)
(* TLAPS is not yet capable of proving liveness properties.                *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})
  (*************************************************************************)
  (* The invariance of TypeOK is obvious.  (I decided to make the obvious  *)
  (* fact that pc equals "Done" only if vroot is empty part of the         *)
  (* type-correctness invariant.)                                          *)
  (*************************************************************************)

Inv1 == /\ TypeOK  
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)
  (*************************************************************************)
  (* The second conjunct of Inv1 is invariant because each element of      *)
  (* Succ[n] is added to vroot when n is added to `marked', and it remains *)
  (* in vroot at least until it's added to `marked'.                        *)
  (*************************************************************************)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)
  (*************************************************************************)
  (* Since ReachableFrom(marked \cup vroot) is the union of                *)
  (* ReachableFrom(marked) and ReachableFrom(vroot), to prove that Inv2 is *)
  (* invariant we must show ReachableFrom(marked) is a subset of           *)
  (* marked \cup ReachableFrom(vroot).                                     *)
  (*                                                                       *)
  (* Since m is in ReachableFrom(marked), there is a path from some node  *)
  (* in `marked' to m.  Either m itself is in `marked' or some node on     *)
  (* that path is not in `marked' yet is reachable from a node in vroot.   *)
  (*************************************************************************)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)
  (*************************************************************************)
  (* For convenience, let R equal marked \cup ReachableFrom(vroot).  In    *)
  (* the initial state, marked = {} and vroot = {Root}, so R equals        *)
  (* Reachable and Inv3 is true.  Each action `a' leaves R unchanged:       *)
  (* either it moves a node from vroot to `marked' or it removes a node    *)
  (* from vroot that has no successors outside vroot, which is already in *)
  (* ReachableFrom(vroot) once it is in `marked'.  In either case, R is    *)
  (* unchanged.)                                                          *)
  (*************************************************************************)

PartialCorrectness == (pc = "Done") => (marked = Reachable)
THEOREM Spec => []PartialCorrectness
  (*************************************************************************)
  (* TypeOK implies (pc = "Done") => (vroot = {}), and ReachableFrom({}) = *)
  (* {}.  Hence Inv3 implies (vroot = {}) => (marked = Reachable).  Since *)
  (* Inv3 is invariant, the theorem follows.                              *)
  (*************************************************************************)

(***************************************************************************)
(* This theorem asserts that if the set of nodes reachable from Root is    *)
(* finite, then the algorithm eventually terminates.  Spec => <>(pc =     *)
(* "Done") follows from weak fairness of Next and the finiteness of the    *)
(* set of reachable nodes.                                                  *)
(***************************************************************************)
THEOREM ASSUME IsFiniteSet(Reachable) PROVE Spec => <>(pc = "Done")
  (*************************************************************************)
  (* By weak fairness of Next, to prove <>(pc = "Done") it suffices to     *)
  (* prove <>(vroot = {}).  If vroot were never empty, an infinite number  *)
  (* of `a' steps would keep adding new nodes to `marked', which is       *)
  (* impossible because Reachable is finite and `marked' is contained in  *)
  (* it.                                                                    *)
  (*************************************************************************)

=============================================================================