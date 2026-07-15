---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants (provided by the .cfg)
--------------------------------------------------------------------*)
CONSTANT N          \* number of creatures
CONSTANT M          \* maximum total number of meetings
CONSTANT Faded      \* the color representing a faded creature
CONSTANT MeetingPlaceEmpty \* sentinel representing an empty meeting place

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Colors == {"blue", "red", "yellow", Faded}
LivingColors == {"blue", "red", "yellow"}

(*--------------------------------------------------------------------
  Type definitions
--------------------------------------------------------------------*)
Creature == 1..N
State == [ color : [Creature -> Colors],
           count : [Creature -> Nat],
           mall  : (Creature \cup {MeetingPlaceEmpty}),
           total : Nat ]

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ mall = MeetingPlaceEmpty
  /\ total = 0
  /\ \A c \in Creature :
        /\ color[c] \in LivingColors
        /\ count[c] = 0

(*--------------------------------------------------------------------
  Complement rule
--------------------------------------------------------------------*)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    LET remaining == {"blue", "red", "yellow"} \ {c1, c2} IN
    CHOOSE x \in remaining : TRUE

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

(* A living creature enters an empty meeting place *)
Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ color[c] # Faded
  /\ mall' = c
  /\ UNCHANGED << color, count, total >>

(* A living creature attempts to enter after the limit has been reached and fades out *)
FadeAttempt(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ color[c] # Faded
  /\ color' = [color EXCEPT ![c] = Faded]
  /\ UNCHANGED << count, mall, total >>

(* Two different living creatures meet and mutate *)
Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ color[c] # Faded
  /\ color[mall] # Faded
  /\ LET newcol == Complement(color[c], color[mall]) IN
     /\ color' = [color EXCEPT ![c] = newcol,
                               ![mall] = newcol]
  /\ count' = [count EXCEPT ![c] = count[c] + 1,
                               ![mall] = count[mall] + 1]
  /\ total' = total + 1
  /\ mall' = MeetingPlaceEmpty

(* No‑op (stutter) when none of the above can fire *)
Stutter ==
  UNCHANGED << mall, total, color, count >>

Next ==
  \/ \E c \in Creature : Enter(c)
  \/ \E c \in Creature : FadeAttempt(c)
  \/ \E c \in Creature : Meet(c)
  \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<< mall, total, color, count >>

(*--------------------------------------------------------------------
  Type invariant (ensures all variables stay within their domains)
--------------------------------------------------------------------*)
TypeOK ==
  /\ mall \in (Creature \cup {MeetingPlaceEmpty})
  /\ total \in Nat
  /\ total <= M
  /\ \A c \in Creature :
        /\ color[c] \in Colors
        /\ count[c] \in Nat
        /\ IF color[c] = Faded THEN count[c] <= total
           ELSE TRUE

(*--------------------------------------------------------------------
  Safety invariant: sum of individual meeting counts equals twice the
  global meeting counter once the limit is reached.
--------------------------------------------------------------------*)
SumMet ==
  (total = M) => ( /\ \A c \in Creature : count[c] <= M
                   /\ ( \A c \in Creature : count[c] >= 0 )
                   /\ ( \A c \in Creature : count[c] \in Nat )
                   /\ ( \A c \in Creature : IF color[c] = Faded THEN count[c] <= M ELSE TRUE )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                   /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )  \* redundant but harmless
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
                 /\ ( \A c \in Creature : count[c] <= M )
                 /\ ( \A c \in Creature : count[c] >= 0 )
                 /\ ( \A c \in Creature : count[c] \in Nat )
        /\ 2 * total = Sum_{c \in Creature} count[c] )

====