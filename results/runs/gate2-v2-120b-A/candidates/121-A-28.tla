---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

(* ----------------------------------------------------------------------
   Constants (to be bound in the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANT CharacterSet \* a subset of Nat representing the alphabet
CONSTANT Nat \* the set of natural numbers (used as a sentinel)

(* ----------------------------------------------------------------------
   Derived constants
   ---------------------------------------------------------------------- *)
Sentinel == Nat \ { i \in Nat : i \in 0 .. MaxStringLen } \* any natural not used as an index

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES
    InputString,      \* the circular string, a sequence of characters
    Len,              \* its length
    Failure,          \* failure function array: [0..2*Len -> Nat \cup {Sentinel}]
    P,                \* pattern-match index (current failure function lookup)
    I,                \* outer loop counter (1 .. 2*Len)
    Best,             \* best rotation offset (0 .. Len-1)
    pc                \* program counter (labels of algorithm steps)

(* ----------------------------------------------------------------------
   Helper definition for indexed access with modulo wrap‑around
   ---------------------------------------------------------------------- *)
CharAt(i) == InputString[ (i % Len) + 1 ]

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ InputString \in Seq(CharacterSet) /\ Len = Len(InputString)
    /\ Failure = [j \in 0..2*Len |-> Sentinel]
    /\ P = Sentinel
    /\ I = 1
    /\ Best = 0
    /\ pc = "OuterCheck"

(* ----------------------------------------------------------------------
   Actions (labeled steps of Booth's algorithm)
   ---------------------------------------------------------------------- *)

OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF I < 2*Len THEN
          /\ pc' = "Lookup"
       ELSE
          /\ pc' = "Done"
    /\ UNCHANGED <<InputString, Len, Failure, P, I, Best>>

Lookup ==
    /\ pc = "Lookup"
    /\ P' = Failure[(I - Best) % Len]
    /\ pc' = "Compare"
    /\ UNCHANGED <<InputString, Len, Failure, I, Best>>

Compare ==
    /\ pc = "Compare"
    /\ IF CharAt(I) = CharAt(I + P) THEN
          /\ pc' = "UpdateAfterMatch"
       ELSE
          /\ pc' = "InnerLoop"
    /\ UNCHANGED <<InputString, Len, Failure, I, Best, P>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF P = Sentinel THEN
          /\ pc' = "PostCompare"
       ELSE IF CharAt(I) < CharAt(I + P) THEN
          /\ Best' = I
          /\ P' = Sentinel
          /\ pc' = "UpdateFailure"
       ELSE
          /\ P' = Failure[P]
          /\ pc' = "InnerLoop"
    /\ UNCHANGED <<InputString, Len, Failure, I>>

UpdateAfterMatch ==
    /\ pc = "UpdateAfterMatch"
    /\ Failure' = [Failure EXCEPT ![I - Best] = P + 1]
    /\ P' = Failure[(I - Best) % Len]
    /\ pc' = "IncI"
    /\ UNCHANGED <<InputString, Len, I, Best>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ IF CharAt(I) < CharAt(I + P) THEN
          /\ Best' = I
          /\ Failure' = [Failure EXCEPT ![I - Best] = Sentinel]
       ELSE
          /\ Failure' = [Failure EXCEPT ![I - Best] = Sentinel]
    /\ P' = Sentinel
    /\ pc' = "IncI"
    /\ UNCHANGED <<InputString, Len, I>>

IncI ==
    /\ pc = "IncI"
    /\ I' = I + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<InputString, Len, Failure, P, Best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<InputString, Len, Failure, P, I, Best, pc>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<InputString, Len, Failure, P, I, Best, pc>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ OuterCheck
    \/ Lookup
    \/ Compare
    \/ InnerLoop
    \/ UpdateAfterMatch
    \/ PostCompare
    \/ IncI
    \/ Stutter

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<InputString, Len, Failure, P, I, Best, pc>>

(* ----------------------------------------------------------------------
   Type invariant (ensures variables stay within their domains)
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ InputString \in Seq(CharacterSet)
    /\ Len = Len(InputString)
    /\ Failure \in [0..2*Len -> Nat \cup {Sentinel}]
    /\ P \in Nat \cup {Sentinel}
    /\ I \in 1..2*Len
    /\ Best \in 0..Len-1
    /\ pc \in {"OuterCheck","Lookup","Compare","InnerLoop",
               "UpdateAfterMatch","PostCompare","IncI","Done"}

(* ----------------------------------------------------------------------
   Correctness invariant
   ---------------------------------------------------------------------- *)
Correctness ==
    /\ \A j \in 0..Len-1 :
          LexicographicLe(
            SubSeq(InputString, Best+1, Len) \o SubSeq(InputString, 1, Best),
            SubSeq(InputString, j+1, Len) \o SubSeq(InputString, 1, j))
    /\ \A k \in 0..Len-1 :
          ( SubSeq(InputString, Best+1, Len) \o SubSeq(InputString, 1, Best) =
            SubSeq(InputString, k+1, Len) \o SubSeq(InputString, 1, k) )
          => Best <= k

(* ----------------------------------------------------------------------
   Liveness (termination) property – optional for completeness
   ---------------------------------------------------------------------- *)
Termination == <> (pc = "Done")

=============================================================================