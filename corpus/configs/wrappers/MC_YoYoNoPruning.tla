---- MODULE MC_YoYoNoPruning ----
(* Hand-authored (no upstream/sibling wrapper found). Nodes/Edges must form a
   strongly-connected undirected graph per the module's own ASSUME. A
   triangle is the simplest non-trivial example. *)
EXTENDS YoYoNoPruning
NodesConst == {1, 2, 3}
EdgesConst == {{1, 2}, {2, 3}, {1, 3}}
====
