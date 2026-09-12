---- MODULE W4Od10m7p4t2 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Controllers, Blocks, PoolCap, NoBlock, NoRead

VARIABLES
  energised,  %% the number of blocks currently energised
  latched,    %% the latched snapshot of energised
  refused,    %% the refused status of each controller
  claimed     %% the claimed block of each controller

TypeOK ==
  energised \in 0..PoolCap
  refused \in [Controllers -> BOOLEAN]
  claimed \in [Controllers -> Blocks \cup {NoBlock}]
  latched = energised

Init ==
  energised = 0
  \A c \in Controllers : refused[c] = FALSE
  \A c \in Controllers : claimed[c] = NoBlock

Next ==
  \E c \in Controllers :
    \E b \in Blocks :
      (claimed[c] = b /\ refused[c] = FALSE) /\ claimed' = claimed \cup {[c |-> b]} \cup {[c' \in Controllers : c' \neq c |-> claimed[c']]}
    \/ \E c \in Controllers :
      (claimed[c] = NoBlock /\ refused[c] = FALSE) /\ claimed' = claimed \cup {[c |-> NoBlock]}
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ latched[c] = energised) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised = PoolCap) /\ refused' = refused \cup {[c |-> TRUE]}
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ latched[c] # energised) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ latched[c] # energised /\ energised < latched[c]) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ latched[c] # energised /\ energised = latched[c]) /\ refused' = refused \cup {[c |-> TRUE]}
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ latched[c] # energised /\ energised > latched[c]) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = TRUE) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < latched[c]) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised > latched[c]) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised = latched[c]) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < latched[c]) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised > latched[c]) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised = latched[c]) /\ claimed' = claimed
    \/ \E c \in Controllers :
      (claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < PoolCap) /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < latched[c] /\ energised > 0 /\ energised < PoolCap /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised > latched[c] /\ energised > 0 /\ energised < PoolCap /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised = latched[c] /\ energised > 0 /\ energised < PoolCap /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < PoolCap /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised > latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised = latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < PoolCap /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised > latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised = latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < PoolCap /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised > latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised = latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < PoolCap /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised > latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised = latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < PoolCap /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised < latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised > latched[c] /\ energised > 0 /\ claimed' = claimed
    \/ \E c \in Controllers :
      claimed[c] # NoBlock /\ refused[c] = FALSE /\ energised < PoolCap /\ claimed[c] # NoBlock /\ energised = l