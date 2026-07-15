---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--algorithm MisraSeq
variables
  marked = {},
  frontier = {},
  pc = "Done"; \* placeholder, actual pc values defined below

begin
  while pc # "Done" do
    either pc = "Init" ->
        \* No action here, we rely on Init predicate below
        pc := "Done"
      or other -> 
        pc := "Done"
    end either;
  end while;
end algorithm; *)

VARIABLES marked, frontier, pc

(* ------------------------------------------------------------------- *)
(* CONSTANTS (must be instantiated by the .cfg)                         *)
CONSTANTS Nodes, Root, Succ, Seq

(* ------------------------------------------------------------------- *)
(* State space definition                                               *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Init", "Step", "Done"}

(* ------------------------------------------------------------------- *)
(* Initial state (inherits from the algorithm specification)           *)
Init ==
  /\ pc = "Init"
  /\ marked = {}
  /\ frontier = {Root}

(* ------------------------------------------------------------------- *)
(* Actions (inherit from the sequential reachability algorithm)        *)

(* Process one frontier node, adding its successors to marked and frontier *)
Step ==
  /\ pc = "Init"
  /\ frontier # {}
  /\ \E n \in frontier :
        /\ marked'   = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup Succ[n]
        /\ pc'       = "Init"
  /\ UNCHANGED << >>

(* When frontier empty, algorithm is done *)
Done ==
  /\ pc = "Init"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED << marked, frontier >>

(* ------------------------------------------------------------------- *)
(* Next-state relation                                                  *)
Next ==
  \/ Step
  \/ Done

(* ------------------------------------------------------------------- *)
(* Specification                                                       *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ------------------------------------------------------------------- *)
(* Invariants                                                          *)

(* Inv1: Successor closure – every marked node's successors are either
   already marked or will eventually be in the frontier. *)
Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

(* Inv2: Reachability decomposition – any node is either marked,
   currently in the frontier, or unreachable from Root. *)
Inv2 ==
  \A n \in Nodes :
    n \in marked \/ n \in frontier \/ ~(\E seq \in Seq :
        /\ Len(seq) >= 1
        /\ seq[1] = Root
        /\ seq[Len(seq)] = n
        /\ \A i \in 1..Len(seq)-1 : seq[i+1] \in Succ[seq[i]])

(* Inv3: Reachable set equality – the set of marked nodes equals the set
   of nodes that have a finite path from Root. *)
Inv3 ==
  marked =
    { n \in Nodes :
        \E seq \in Seq :
          /\ Len(seq) >= 1
          /\ seq[1] = Root
          /\ seq[Len(seq)] = n
          /\ \A i \in 1..Len(seq)-1 : seq[i+1] \in Succ[seq[i]] }

(* PartialCorrectness – when the algorithm terminates, all reachable nodes are marked. *)
PartialCorrectness ==
  pc = "Done" => marked = { n \in Nodes :
        \E seq \in Seq :
          /\ Len(seq) >= 1
          /\ seq[1] = Root
          /\ seq[Len(seq)] = n
          /\ \A i \in 1..Len(seq)-1 : seq[i+1] \in Succ[seq[i]] }

(* ------------------------------------------------------------------- *)
(* Liveness property (termination)                                      *)
Termination ==
  <> (pc = "Done")

====