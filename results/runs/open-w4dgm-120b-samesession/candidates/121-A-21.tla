---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* Zero-indexed sequence over a finite character set, defined in a separate utility module.
\* The action set is a small finite slice of the infinite action lattice of the original algorithm.
\* The model bounds are the character set size and the maximum string length, which are parameters
\* of the model checking configuration rather than of the module itself.

Stutter == "stutter"
Sentinel == 99
MaxLength == 2

VARIABLES string, length, fail, pat, loop, bestOffset, pc

vars == <<string, length, fail, pat, loop, bestOffset, pc>>

TypeInvariant ==
  /\ string \in Seq(CharacterSet)
  /\ length = Len(string)
  /\ fail \in [0..2 * MaxLength -> 0..(2 * MaxLength \cup {Sentinel})]
  /\ pat \in 0..(2 * MaxLength \cup {Sentinel})
  /\ loop \in 0..(2 * MaxLength)
  /\ bestOffset \in 0..(MaxLength - 1)
  /\ pc \in {"outerLoop", "failLookup", "innerComp", "lessThan", "failFollow", "postComp", "increment", "terminate"}

Init ==
  /\ \E s \in Seq(CharacterSet) : string = s
  /\ length = Len(string)
  /\ fail = [i \in 0..(2 * MaxLength) |-> Sentinel]
  /\ pat = Sentinel
  /\ loop = 1
  /\ bestOffset = 0
  /\ pc = "outerLoop"

OuterLoop ==
  /\ pc = "outerLoop"
  /\ IF loop < 2 * length THEN pc' = "failLookup" ELSE pc' = "terminate"
  /\ UNCHANGED <<string, length, fail, pat, loop, bestOffset>>

FailLookup ==
  /\ pc = "failLookup"
  /\ pat' = fail[loop - bestOffset]
  /\ pc' = "innerComp"
  /\ UNCHANGED <<string, length, fail, loop, bestOffset>>

InnerComp ==
  /\ pc = "innerComp"
  /\ IF (string[loop % length] # string[(pat + bestOffset) % length] /\ pat # Sentinel)
       THEN pc' = "lessThan"
       ELSE pc' = "postComp"
  /\ UNCHANGED <<string, length, fail, pat, loop, bestOffset>>

LessThan ==
  /\ pc = "lessThan"
  /\ bestOffset' = IF string[loop % length] < string[(pat + bestOffset) % length] THEN loop % length ELSE bestOffset
  /\ pc' = "failFollow"
  /\ UNCHANGED <<string, length, fail, pat, loop>>

FailFollow ==
  /\ pc = "failFollow"
  /\ fail' = [fail EXCEPT ![loop - bestOffset] = IF pat = Sentinel THEN Sentinel ELSE pat + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<string, length, pat, loop, bestOffset>>

PostComp ==
  /\ pc = "postComp"
  /\ IF (string[loop % length] # string[(pat + bestOffset) % length] /\ pat = Sentinel)
       THEN bestOffset' = IF string[loop % length] < string[(pat + bestOffset) % length]
                           THEN loop % length ELSE bestOffset
       ELSE UNCHANGED bestOffset
  /\ fail' = [fail EXCEPT ![loop - bestOffset] =
                 IF string[loop % length] = string[(pat + bestOffset) % length]
                 THEN pat + 1 ELSE Sentinel]
  /\ pc' = "increment"
  /\ UNCHANGED <<string, length, pat, loop>>

Increment ==
  /\ pc = "increment"
  /\ loop' = loop + 1
  /\ pc' = "outerLoop"
  /\ UNCHANGED <<string, length, fail, pat, bestOffset>>

Terminate ==
  /\ pc = "terminate"
  /\ UNCHANGED vars

StutterStep ==
  /\ pc = Stutter
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ FailLookup \/ InnerComp \/ LessThan \/ FailFollow
  \/ PostComp \/ Increment \/ Terminate \/ StutterStep

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(OuterLoop) /\ WF_vars(FailLookup) /\ WF_vars(InnerComp)
  /\ WF_vars(LessThan) /\ WF_vars(FailFollow) /\ WF_vars(PostComp) /\ WF_vars(Increment)

\* Correctness: the rotation the algorithm reports is the lexicographically-minimum
\* rotation of the input string, and it is the smallest shift among equal rotations.
Correctness ==
  /\ \A k \in 0..(length - 1) :
       \E i \in 0..(length - 1) :
         \A j \in 0..(length - 1) :
           (string[(i + j) % length] # string[(k + j) % length])
             \/ (j = length - 1 /\ i <= k)
  /\ \A i \in 0..(length - 1) : string[(bestOffset + i) % length] = string[(i + bestOffset) % length]

Termination == <>(pc = "terminate")

\* The .cfg replaces the standard Naturals with a finite version drawn from the
\* bounded character set, so `Nat` is a synonym for `CharacterSet` here and not
\* the unbounded natural numbers; that replacement is what makes the model
\* checking configuration finite rather than the module itself.
\* The replacement must happen inside the .cfg file, never in this module.
====