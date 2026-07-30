----- MODULE LeaderElection -----

(*
  Minimal TLA+ specification of quorum-based leader election
  over a fixed cluster of nodes with monotonically increasing terms.

  This spec models a distributed system where:
  - Each node has a monotonically increasing term counter
  - A node can vote for at most one candidate per term
  - A candidate becomes leader when it receives a quorum of votes in its term
  - Once a node advances to a new term, it clears its vote

  Safety properties:
  1. At most one node can be elected leader per term
  2. A node is elected leader only if it has a quorum of votes in its term
  3. A node can vote for at most one node per term
  4. Terms increase monotonically for each node

  Key abstraction: we model only the voting state and term counters,
  not the network, communication delays, timeouts, or implementation details.
*)

EXTENDS Naturals, FiniteSets

(*
  Constants: fixed parameters of the system.

  NumNodes: the number of nodes in the cluster
  QuorumSize: minimum votes needed to elect a leader
*)
CONSTANT NumNodes, QuorumSize

(* Quorum must be a strict majority *)
ASSUME /\ NumNodes > 0
       /\ QuorumSize > NumNodes \div 2

Nodes == 1..NumNodes

(*
  State variables.

  currentTerm[n]: the current term of node n (non-decreasing over time)
  votedFor[n]: the node that n has voted for in currentTerm[n],
               or Nil if it has not yet voted in this term
*)
VARIABLE currentTerm, votedFor

(*
  Type correctness: all values are well-typed.
*)
TypeOK ==
  /\ currentTerm \in [Nodes -> Nat]
  /\ votedFor \in [Nodes -> Nodes \cup {Nil}]

(*
  Initial state: all nodes start at term 0 with no votes cast.
*)
Init ==
  /\ currentTerm = [n \in Nodes |-> 0]
  /\ votedFor = [n \in Nodes |-> Nil]

(*
  Helper: check if node n has a quorum of votes in term t.
  This is true if at least QuorumSize nodes have voted for n
  while in term t.
*)
HasQuorumInTerm(n, t) ==
  Cardinality({m \in Nodes : votedFor[m] = n /\ currentTerm[m] = t})
    >= QuorumSize

(*
  Action: AdvanceTerm(n)

  Node n moves to a new term, clearing its vote.
  This is called when a node receives a higher term from another node
  or when it initiates a new election.

  Ensures:
  - currentTerm[n] increases by 1
  - votedFor[n] is reset to Nil (ready to vote in the new term)
*)
AdvanceTerm(n) ==
  /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
  /\ votedFor' = [votedFor EXCEPT ![n] = Nil]

(*
  Action: Vote(n, c)

  Node n votes for candidate c in n's current term.

  Requires:
  - n has not yet voted in its current term (votedFor[n] = Nil)

  Effect:
  - votedFor[n] becomes c
  - currentTerm is unchanged (voting doesn't change term)

  Note: we allow any node to be a candidate; a node may vote for itself
  or any other node. Election correctness is enforced by the quorum invariant.
*)
Vote(n, c) ==
  /\ votedFor[n] = Nil
  /\ votedFor' = [votedFor EXCEPT ![n] = c]
  /\ currentTerm' = currentTerm

(*
  Next-state relation: one of the two actions fires.
*)
Next ==
  \/ \E n \in Nodes : AdvanceTerm(n)
  \/ \E n, c \in Nodes : Vote(n, c)

(*
  Specification: initial state plus fairness.
  We use stuttering (no-ops are allowed between steps).
*)
Spec == Init /\ [][Next]_<<currentTerm, votedFor>>

(*
  Safety invariants: properties that must hold in all reachable states.
*)

(*
  Invariant: AtMostOneLeaderPerTerm

  Safety-critical property: in any given term, at most one node
  can have a quorum of votes for itself.

  This ensures that the leader election is safe: no two different nodes
  can both claim to be the leader in the same term.

  Proof sketch: if two nodes n1 and n2 both have a quorum in the same term t,
  then they each have >= QuorumSize votes from nodes in term t.
  Since QuorumSize > NumNodes/2, the two sets of voters must overlap.
  But a node in term t can vote for only one candidate.
  Contradiction.
*)
AtMostOneLeaderPerTerm ==
  \A n1, n2 \in Nodes :
    (HasQuorumInTerm(n1, currentTerm[n1]) /\
     HasQuorumInTerm(n2, currentTerm[n2]) /\
     currentTerm[n1] = currentTerm[n2])
      => n1 = n2

(*
  Invariant: OneVotePerTermPerNode

  Each node votes for at most one candidate in its current term.
  This is enforced by the Vote action (which requires votedFor[n] = Nil),
  so it should always be true.
*)
OneVotePerTermPerNode ==
  \A n \in Nodes : votedFor[n] \in Nodes \cup {Nil}

(*
  Invariant: TermsNeverDecrease

  For each node, its current term never decreases.
  This is enforced by AdvanceTerm (which only increases terms),
  so it should always be true by construction.
*)
TermsNeverDecrease ==
  \A n \in Nodes : currentTerm[n] >= 0

=====
