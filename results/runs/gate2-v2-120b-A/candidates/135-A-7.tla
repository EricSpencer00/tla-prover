---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(*  Constants required by the .cfg file                                    *)
(***************************************************************************)
CONSTANTS
    Nodes,      \* The finite set of node identifiers
    Root,       \* The distinguished start node
    Succ,       \* Succ \in [Nodes -> SUBSET Nodes] gives the successors of each node
    Seq         \* An override type for finite sequences over Nodes

(***************************************************************************)
(*  Derived definitions                                                   *)
(***************************************************************************)

\* The set of all finite sequences over Nodes (used to define Seq)
SeqAll == { s \in Seq(Node) : Len(s) <= Cardinality(Nodes) }

\* Helper to coerce the constant Seq to the actual set of sequences we allow
Seq == SeqAll

\* The length bound for sequences (equal to the number of nodes)
SeqBound == Cardinality(Nodes)

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)
VARIABLES
    Marked,      \* Set of nodes that have been discovered
    Frontier,   \* Set of nodes whose successors are yet to be explored
    pc          \* Program counter (identifies the current step of the algorithm)

(***************************************************************************)
(*  Initialization                                                       *)
(***************************************************************************)
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "Loop"

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

Loop ==
    /\ pc = "Loop"
    /\ Frontier # {}          \* There are nodes to explore
    /\ \E n \in Frontier :
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup (Succ[n] \ Marked)
        /\ pc' = "Loop"

Done ==
    /\ pc = "Loop"
    /\ Frontier = {}
    /\ Marked' = Marked
    /\ Frontier' = Frontier
    /\ pc' = "Done"

Termination ==
    /\ pc = "Done"

Next ==
    \/ Loop
    \/ Done

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
Spec ==
    Init /\ [][Next]_<<Marked, Frontier, pc>>

(***************************************************************************)
(*  Safety invariants                                                     *)
(***************************************************************************)

\* Type correctness: variables stay within their intended domains
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"Loop", "Done"}

\* Inv1: Successor closure – every successor of a marked node is either marked
Inv1 ==
    \A n \in Marked : \A s \in Succ[n] : s \in Marked

\* Inv2: Reachability decomposition – the marked set together with the frontier
\*      equals the set of nodes reachable from the root via a path of length
\*      at most the sequence bound.
Inv2 ==
    \A n \in Nodes :
        (n \in Marked \cup Frontier) =
        \E s \in Seq :
            /\ Len(s) <= SeqBound
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]

\* Inv3: Reachable set equality – once the algorithm finishes, the marked set
\*      equals the set of all nodes reachable from the root.
Inv3 ==
    /\ pc = "Done"
    /\ Marked = { n \in Nodes :
                    \E s \in Seq :
                        /\ Len(s) <= SeqBound
                        /\ s[1] = Root
                        /\ s[Len(s)] = n
                        /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]] }

\* PartialCorrectness – the algorithm never declares termination before all
\* reachable nodes are marked.
PartialCorrectness ==
    /\ pc = "Done"
    => \A n \in Nodes :
           ( \E s \in Seq :
               /\ Len(s) <= SeqBound
               /\ s[1] = Root
               /\ s[Len(s)] = n
               /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
           ) => n \in Marked

(***************************************************************************)
(*  The theorem to be checked (optional, but convenient)                   *)
(***************************************************************************)
THEOREM Spec => []TypeOK /\ []Inv1 /\ []Inv2 /\ []Inv3 /\ []PartialCorrectness

(***************************************************************************)
(*  Configuration for TLC (not part of the module, but useful for context) *)
(***************************************************************************)
\* The .cfg file would contain:
\*   CONSTANTS
\*       Nodes = {1, 2, 3, 4}
\*       Root = 1
\*       Succ = [1 |-> {2,3},
\*               2 |-> {3,4},
\*               3 |-> {1,4},
\*               4 |-> {2,1}]
\*   SPECIFICATION Spec
\*   INVARIANT TypeOK
\*   INVARIANT Inv1
\*   INVARIANT Inv2
\*   INVARIANT Inv3
\*   INVARIANT PartialCorrectness
\*   PROPERTY Termination

====