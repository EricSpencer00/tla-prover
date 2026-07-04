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

(* The set of reachable nodes is finite because the underlying graph has
   a finite set of nodes.  Adding this explicit assumption makes the
   termination proof unconditional for the finite models used in TLC. *)
ASSUME FiniteReachable == IsFiniteSet(Reachable)

---------------------------------------------------------------------------
(***************************************************************************
The obvious algorithm for computing Reachable({Root}) is as follows.
There are two variables which, following Misra, we call `marked' and
vroot.  Each variable holds a set of nodes that are reachable from
Root.  Initially, marked = {} and vroot = {Root}.  While vroot is
non-empty, the obvious algorithm removed an arbitrary node v from
vroot, adds v to `marked', and adds to vroot all nodes in Succ[v] that
are not in `marked'.  The algorithm terminates when vroot is empty,
which will eventually be the case if and only if Reachable({Root}) is a
finite set.  When it terminates, `marked' equals Reachable({Root}).

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
                /\ pc' = "a"
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
(* invariance, as well of proofs of the two theorems that assert           *)
(* correctness of the algorithm.  The module ReachableProofs contains      *)
(* rigorous, TLAPS checked TLA+ proofs of all except the last theorem.     *)
(* The last theorem asserts termination, which is a liveness property, and *)
(* TLAPS is not yet capable of proving liveness properties.                *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK  
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)

PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

THEM

  ASSUME IsFiniteSet(Reachable)
  PROVE  Spec => <>(pc = "Done")

====