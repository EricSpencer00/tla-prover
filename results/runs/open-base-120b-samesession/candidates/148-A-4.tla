---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock,
    PrivToPub

(* Sentinel aliases *)
NoHash == NoHashVal
NoBlock == NoBlockVal

VARIABLES
    lastHash, ledger, received

(*-----------------------------------------------------------------
  Block structure
-----------------------------------------------------------------*)
Block ==
    [ kind   : {"genesis","send","open","receive","change"},
      account: PublicKey,
      prev   : Hash,
      dest   : PublicKey,
      amount : Nat,
      rep    : PublicKey,
      sig    : STRING ]

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]
    /\ \A n \in Node:
         \A h \in Hash:
            ledger[n][h] \in Block \/ ledger[n][h] = NoBlock

(*-----------------------------------------------------------------
  Cryptographic helpers (abstract)
-----------------------------------------------------------------*)
Owner(b) == b.account
ValidSignature(b) == TRUE   \* placeholder for a real check

SafetyInvariant ==
    \A n \in Node:
        \A h \in Hash:
            IF ledger[n][h] = NoBlock
            THEN TRUE
            ELSE Owner(ledger[n][h]) \in PublicKey
                 /\ ValidSignature(ledger[n][h])

(*-----------------------------------------------------------------
  Hash calculation (abstract, overridden in the .cfg)
-----------------------------------------------------------------*)
CalculateHashImpl(b) == CalculateHash(b)
CalculateHash(b) == CalculateHashImpl(b)

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
CreateGenesis ==
    /\ lastHash = NoHash
    \E n \in Node, pk \in PrivateKey, h \in Hash:
        /\ h # NoHash
        /\ let blk ==
                [ kind    |-> "genesis",
                  account |-> PrivToPub[pk],
                  prev    |-> NoHash,
                  dest    |-> NoHash,
                  amount  |-> GenesisBalance,
                  rep     |-> NoHash,
                  sig     |-> "sig" ] in
           /\ lastHash' = h
           /\ ledger' = [m \in Node |-> [hh \in Hash |-> IF hh = h THEN blk ELSE ledger[m][hh]]]
           /\ received' = received
           /\ UNCHANGED << >>

ProcessReceived ==
    \E n \in Node, h \in received[n]:
        /\ ledger' = ledger
        /\ received' = [m \in Node |-> IF m = n THEN received[m] \ {h} ELSE received[m]]
        /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesis
    \/ ProcessReceived

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<lastHash, ledger, received>>

====