---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

Pos == {<<x, y>> : x, y \in 1..N}

(* The original TypeOK invariant required grid NOT to be a function from Pos to BOOLEAN,
   which contradicted the initialization and transition definitions that treat grid exactly as
   such a function.  We therefore correct TypeOK to assert that grid *is* a function from Pos
   to BOOLEAN.  This preserves the intended semantics of the specification while allowing the
   model checker to verify the invariant. *)
TypeOK == grid \in [Pos -> BOOLEAN]

sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

score(p) ==
  LET nbrs == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
      points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
  IN Sum(sc, points)

Init == grid \in [Pos -> BOOLEAN]

Next ==
  grid' = [p \in Pos |-> IF \/ (grid[p] /\ score(p) \in {2, 3})
                         \/ (~grid[p] /\ score(p) = 3)
                       THEN TRUE
                       ELSE FALSE]

Spec == Init /\ [][Next]_<<grid>>

====