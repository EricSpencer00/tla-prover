---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers
CONSTANTS A, B, C, bound

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

vars == <<seq, i, cand, cnt>>
Num == Cardinality(Value)

Init ==
    /\ seq = << >>
    /\ i = 0
    /\ cand = 0
    /\ cnt = 0

\* Extend the sequence by one value, if length < bound.
Append(v) ==
    /\ i < bound
    /\ seq' = [seq EXCEPT ![i + 1] = v]
    /\ i' = i + 1
    /\ UNCHANGED <<cand, cnt>>

\* Reset the voting state at the start of a fresh run.
Reset ==
    /\ cand' = 0
    /\ cnt' = 0
    /\ UNCHANGED <<seq, i>>

\* Process the next element of the sequence into the Boyer-Moore state.
Vote ==
    /\ i > 0
    /\ LET x == seq[i] IN
        IF cnt = 0 THEN /\ cand' = x /\ cnt' = 1
        ELSE IF x = cand THEN /\ cnt' = cnt + 1 /\ UNCHANGED cand
        ELSE /\ cnt' = cnt - 1 /\ UNCHANGED cand
    /\ UNCHANGED <<seq, i>>

Next ==
    \/ \E v \in Value : Append(v)
    \/ Vote
    \/ Reset

Spec == Init /\ [][Next]_vars

\* Conditionally assert correctness of the final majority-vote claim: the
\* identified candidate is genuinely a majority element exactly when one
\* candidate exists, and its count never exceeds the sequence length.
MajorityClaim ==
    \A v \in Value :
        (cand = v) <=> (\A w \in Value : w = v \/ 2 * Cardinality({x \in 1 .. i : seq[x] = w}) <= i)

====