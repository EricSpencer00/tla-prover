---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences, ZSequences

(* The lexicographically-least circular substring algorithm from Booth's 1980 *)
(* paper, reimplemented as a single deterministic loop with a KMP-style       *)
(* failure function.  The action set is exactly the labeled steps of the       *)
(* algorithm, so the PC trace is a faithful replay of its run.                  *)

CONSTANTS CharacterSet

VARIABLES str, n, fail, pat, k, best, pc

vars == <<str, n, fail, pat, k, best, pc>>

Sentinel == 0
MaxLen == 2

Range(f) == { f[i] : i \in 1..(2 * MaxLen) }

TypeOK ==
  /\ str \in [1..MaxLen -> CharacterSet]
  /\ n = Len(str)
  /\ Range(fail) \subseteq (0..MaxLen) \cup {Sentinel}
  /\ pat \in (0..MaxLen) \cup {Sentinel}
  /\ k \in 1..(2 * MaxLen)
  /\ best \in 0..(n - 1)
  /\ pc \in {"outer", "lookup", "compare", "check", "follow",
             "post", "inc", "done"}

Init ==
  /\ \E s \in [1..MaxLen -> CharacterSet] : str = s
  /\ n = Len(str)
  /\ fail = [i \in 1..(2 * MaxLen) |-> Sentinel]
  /\ pat = Sentinel
  /\ k = 1
  /\ best = 0
  /\ pc = "outer"

Rotate(s, o) == {s[(i + o) % n] : i \in 0..(n - 1)}

LessOrEqual(s, t) ==
  \E i \in 0..(n - 1), j \in 0..(n - 1) :
     /\ \A m \in 0..(n - 1) : s[(i + m) % n] = t[(j + m) % n]
     /\ \A m \in 0..(n - 1) : s[(i + m) % n] = t[(j + m) % n] => m <= j

Outer ==
  /\ pc = "outer"
  /\ pc' = IF k < 2 * n THEN "lookup" ELSE "done"
  /\ UNCHANGED <<str, n, fail, pat, k, best>>

Lookup ==
  /\ pc = "lookup"
  /\ pat' = fail[k - best]
  /\ pc' = "compare"
  /\ UNCHANGED <<str, n, fail, k, best>>

Compare ==
  /\ pc = "compare"
  /\ IF str[(k % n) + 1] = str[((best + k) % n) + 1]
       THEN pc' = "compare"
       ELSE pc' = "check"
  /\ UNCHANGED <<str, n, fail, pat, k, best>>

Check ==
  /\ pc = "check"
  /\ IF pat # Sentinel
       THEN pc' = "follow"
       ELSE pc' = "post"
  /\ UNCHANGED <<str, n, fail, pat, k, best>>

Follow ==
  /\ pc = "follow"
  /\ pat' = fail[pat]
  /\ pc' = "compare"
  /\ UNCHANGED <<str, n, fail, k, best>>

Post ==
  /\ pc = "post"
  /\ IF (str[(k % n) + 1] # str[((best + k) % n) + 1]) /\ (pat = Sentinel)
        /\ str[(k % n) + 1] < str[((best + k) % n) + 1]
       THEN best' = k
       ELSE best' = best
  /\ fail' = [fail EXCEPT ![k - best] =
                IF str[(k % n) + 1] = str[((best + k) % n) + 1]
                  THEN IF pat = Sentinel THEN Sentinel ELSE pat + 1
                  ELSE Sentinel]
  /\ pc' = "inc"
  /\ UNCHANGED <<str, n, pat, k>>

Inc ==
  /\ pc = "inc"
  /\ k' = k + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, n, fail, pat, best>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Outer \/ Lookup \/ Compare \/ Check \/ Follow \/ Post \/ Inc \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Inc)

TypeInvariant == TypeOK

Correctness ==
  /\ Rotate(str, best) \subseteq Rotate(str, 0)
  /\ \A s \in Rotate(str, 0) : Rotate(str, best) \lesseq s

Termination == (pc # "done") ~> (pc = "done")

====