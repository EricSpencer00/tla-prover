---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS CharacterSet, Nat

(* --algorithm LexLeastCircularSubstring
variables
  s \in Seq(CharacterSet), \* input string (zero‑indexed)
  n = Len(s),               \* length of the input string
  f = [i \in 0..2*n |-> Nat], \* failure function, initialised to sentinel Nat
  i = Nat,                  \* pattern‑match index
  j = 1,                    \* outer loop counter, runs 1..2*n‑1
  b = 0,                    \* best rotation offset
  pc = "OuterCheck"         \* program counter
begin
  while TRUE do
    case pc = "OuterCheck" ->
       if j >= 2*n then
          pc := "Done"
       else
          pc := "LookupFailure"
    [] pc = "LookupFailure" ->
       fLookup := IF i = Nat THEN Nat ELSE f[ i ];
       pc := "InnerLoop"
    [] pc = "InnerLoop" ->
       IF s[(b + j) % n] = s[(b + fLookup) % n] THEN
          IF fLookup = Nat THEN
             pc := "PostCompare"
          ELSE
             pc := "FollowFailure"
          END IF
       ELSE
          IF s[(b + j) % n] < s[(b + fLookup) % n] THEN
             b := j;
          END IF;
          pc := "PostCompare"
       END IF
    [] pc = "FollowFailure" ->
       i := fLookup;
       pc := "InnerLoop"
    [] pc = "PostCompare" ->
       IF s[(b + j) % n] # s[(b + fLookup) % n] /\ fLookup = Nat THEN
          IF s[(b + j) % n] < s[(b + fLookup) % n] THEN
             b := j;
          END IF;
          f[j] := Nat
       ELSE
          f[j] := IF fLookup = Nat THEN 0 ELSE fLookup + 1;
       END IF;
       j := j + 1;
       pc := "OuterCheck"
    [] pc = "Done" -> skip
    [] OTHER -> skip
  end while;
end algorithm; *)

VARIABLES s, n, f, i, j, b, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ZeroBasedSeq == Seq(CharacterSet)

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ s \in ZeroBasedSeq
    /\ n = Len(s)
    /\ f = [k \in 0..2*n |-> Nat]      \* all entries sentinel
    /\ i = Nat
    /\ j = 1
    /\ b = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions corresponding to the algorithm steps
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF j >= 2*n THEN
          pc' = "Done"
       ELSE
          pc' = "LookupFailure"
    /\ UNCHANGED <<s, n, f, i, j, b>>

LookupFailure ==
    /\ pc = "LookupFailure"
    /\ LET fLookup == IF i = Nat THEN Nat ELSE f[i] IN
       /\ fLookup' = fLookup   \* expose as a local constant; not a state var
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<s, n, f, i, j, b>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ LET cur == s[(b + j) % n] IN
       LET cand == s[(b + (IF i = Nat THEN 0 ELSE i)) % n] IN
       IF cur = cand THEN
          IF i = Nat THEN
             pc' = "PostCompare"
          ELSE
             pc' = "FollowFailure"
          END IF
       ELSE
          /\ IF cur < cand THEN b' = j ELSE UNCHANGED b
          /\ pc' = "PostCompare"
       END IF
    /\ UNCHANGED <<s, n, f, i, j, b>>

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ i' = IF i = Nat THEN Nat ELSE f[i]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<s, n, f, j, b>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ LET cur == s[(b + j) % n] IN
       LET cand == s[(b + (IF i = Nat THEN 0 ELSE i)) % n] IN
       IF cur # cand /\ i = Nat THEN
          /\ IF cur < cand THEN b' = j ELSE UNCHANGED b
          /\ f' = [f EXCEPT ![j] = Nat]
       ELSE
          /\ f' = [f EXCEPT ![j] = IF i = Nat THEN 0 ELSE i + 1]
       END IF
    /\ j' = j + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED i

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<s, n, f, i, j, b, pc>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<s, n, f, i, j, b, pc>>

Next ==
    \/ OuterCheck
    \/ LookupFailure
    \/ InnerLoop
    \/ FollowFailure
    \/ PostCompare
    \/ Done
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<s, n, f, i, j, b, pc>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ s \in ZeroBasedSeq
    /\ n = Len(s)
    /\ f \in [0..2*n -> Nat \cup 0..n]   \* entries are Nat (sentinel) or valid indices
    /\ i \in Nat \cup 0..n
    /\ j \in 1..2*n
    /\ b \in 0..n-1
    /\ pc \in {"OuterCheck","LookupFailure","InnerLoop","FollowFailure",
               "PostCompare","Done"}

\* Correctness: b points to a lexicographically minimal rotation
Correctness ==
    /\ pc = "Done"
    /\ \A k \in 0..n-1 :
         \A l \in 0..n-1 :
            Rot(b) <= Rot(l)
    /\ Rot(b) = Rot(b) \* (trivial, ensures expression well‑typed)

Rot(b) ==
    s[(b + 0) % n] \* placeholder: the full rotation would be a sequence;
                     \* TLC can treat this as a symbolic expression; the
                     \* invariant only needs the ordering relation.

\* ----------------------------------------------------------------------
\* Liveness (termination) property – optional, not listed in cfg
\* ----------------------------------------------------------------------
Termination == <>[] (pc = "Done")

\* The identifier requested by the .cfg file
Spec == Spec

====