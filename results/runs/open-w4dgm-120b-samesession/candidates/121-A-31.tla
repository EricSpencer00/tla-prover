---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

CONSTANTS CharacterSet

ZSequences == [x \in CharacterSet |-> 1]

VARIABLES str, n, fail, pat, i, best, pc

vars == <<str, n, fail, pat, i, best, pc>>

Sentinel == 255

AllStrings == UNION {[1..m -> CharacterSet] : m \in 1..9}
AllLoops == UNION {1..2m : m \in 1..9}

TypeInvariant ==
  /\ str \in AllStrings
  /\ n = Len(str)
  /\ fail \in [1..AllLoops -> 0..Sentinel]
  /\ pat \in 0..Sentinel
  /\ i \in 1..AllLoops
  /\ best \in 0..(n - 1)
  /\ pc \in {"outer", "lookup", "compare", "update", "follow", "post", "done"}

Spec == Init /\ [][Next]_vars

Init ==
  /\ \E w \in AllStrings : str = w
  /\ n = Len(str)
  /\ fail = [j \in 1..AllLoops |-> Sentinel]
  /\ pat = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "outer"

Outer ==
  /\ pc = "outer"
  /\ IF i < 2 * n THEN pc' = "lookup" ELSE pc' = "done"
  /\ UNCHANGED <<str, n, fail, pat, i, best>>

Lookup ==
  /\ pc = "lookup"
  /\ pat' = fail[i - best + 1]
  /\ pc' = "compare"
  /\ UNCHANGED <<str, n, fail, i, best>>

Compare ==
  /\ pc = "compare"
  /\ IF str[(i % n) + 1] # str[((i - pat) % n) + 1] /\ pat # Sentinel
       THEN pc' = "compare"
       ELSE pc' = "update"
  /\ UNCHANGED <<str, n, fail, pat, i, best>>

Update ==
  /\ pc = "update"
  /\ IF str[i % n + 1] < str[((i - pat) % n) + 1]
       THEN best' = i
       ELSE best' = best
  /\ pc' = "follow"
  /\ UNCHANGED <<str, n, fail, pat, i>>

Follow ==
  /\ pc = "follow"
  /\ fail' = [fail EXCEPT ![i - best + 1] = IF pat = Sentinel THEN Sentinel ELSE pat + 1]
  /\ pc' = "post"
  /\ UNCHANGED <<str, n, pat, i, best>>

Post ==
  /\ pc = "post"
  /\ IF str[i % n + 1] # str[((i - pat) % n) + 1] /\ pat = Sentinel
       THEN best' = IF str[i % n + 1] < str[((i - pat) % n) + 1] THEN i ELSE best
       ELSE best' = best
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, n, fail, pat>>

Terminated ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Outer \/ Lookup \/ Compare \/ Update \/ Follow \/ Post \/ Terminated

Correctness ==
  /\ \A k \in 0..(n - 1) : ((\A j \in 0..(n - 1) : str[((k + j) % n) + 1] <= str[((best + j) % n) + 1])
       \/ (\A j \in 0..(n - 1) : str[((k + j) % n) + 1] = str[((best + j) % n) + 1] => k >= best)

Termination == <>(pc = "done")

====