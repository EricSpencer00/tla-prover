---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

(* --algorithm MisraReachability
variables marked, frontier, pc;

variables marked = {};
variables frontier = {Root};
variables pc = "Init";

define
  Init == /\ marked = {}
          /\ frontier = {Root}
          /\ pc = "Running"
          /\ Unchanged << >>;

  Next == 
    \/ /\ pc = "Running"
       /\ \E v \in frontier :
            /\ marked' = marked \cup {v}
            /\ frontier' = (frontier \ {v}) \cup (Succ[v] \ marked)
            /\ pc' = "Running"
    \/ /\ pc = "Running"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED << marked, frontier >>;

  Termination == /\ pc = "Done"
                 /\ frontier = {}
                 /\ marked = UNION {Succ[n] : n \in Nodes} \cup {Root};
             
  TypeOK == /\ marked \subseteq Nodes
            /\ frontier \subseteq Nodes
            /\ pc \in {"Init", "Running", "Done"};
             
  Inv1 == \A v \in marked : Root \in Seq[<<v>>];
             
  Inv2 == \A v \in Nodes : 
           ( \E s \in Seq : v \in s /\ s[1] = Root ) => v \in marked;
             
  Inv3 == marked = UNION {Seq[<<Root>>] : n \in Nodes};
             
  PartialCorrectness == /\ pc = "Done" => marked = Nodes;
end define;

Spec == Init /\ [][Next]_<<marked, frontier, pc>>
====