---- MODULE MC_YoYoPruning ----
(* Hand-authored (no upstream/sibling wrapper found). Same graph as
   MC_YoYoNoPruning -- a triangle, the simplest strongly-connected
   undirected graph satisfying the module's own ASSUME. *)
EXTENDS YoYoPruning
NodesConst == {1, 2, 3}
EdgesConst == {{1, 2}, {2, 3}, {1, 3}}
====
