---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  CONSTANTS (to be supplied by the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Hash,          \* Set of all possible block hashes
    NoHashVal,     \* Sentinel value of type Hash indicating "no hash"
    PrivateKey,    \* Set of private keys
    PublicKey,    \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total supply of coins at genesis (a natural number)
    NoBlockVal,    \* Sentinel value representing the absence of a block
    CalculateHash, \* Abstract hash calculation operator (will be overridden)
    NoHash,        \* Alias for NoHashVal (required by the description)
    NoBlock        \* Alias for NoBlockVal (required by the description)

(*--------------------------------------------------------------------
  Derived constants / helper mappings (can be instantiated in the .cfg)
--------------------------------------------------------------------*)
\* Mapping from a private key to its corresponding public key
CONSTANT PrivateToPublic

\* Mapping from a node to the private key it owns
CONSTANT NodeToKey

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    lastHash,   \* The most recent block hash (or NoHash)
    ledger,     \* Per‑node copy of the distributed ledger:
                \*   ledger[n][h] = a Block or NoBlock
    received,   \* Per‑node set of hashes that have been received but not yet processed
    Blocks      \* Global mapping from hash to the actual Block (or NoBlock)

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Block ==
    [ type            : {"genesis", "send", "open", "receive", "change"},
      prev            : Hash,
      account         : PublicKey,
      amount          : Nat,
      recipient       : Hash,
      source          : Hash,
      representative  : PublicKey,
      signature       : STRING ]

(*--------------------------------------------------------------------
  Helper operators
--------------------------------------------------------------------*)
\* Abstract signature creation (deterministic for modeling)
Sign(priv, data) == <<priv, data>>

\* Abstract signature verification
VerifySig(pub, blk, sig) ==
    \E priv \in PrivateKey :
        PrivateToPublic[priv] = pub /\ sig = Sign(priv, blk)

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ Blocks = [h \in Hash |-> NoBlock]

(*--------------------------------------------------------------------
  Block creation actions
--------------------------------------------------------------------*)

\* Genesis block creation (can happen only once)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E n \in Node :
        LET priv == NodeToKey[n] IN
        LET pub  == PrivateToPublic[priv] IN
        LET blk  == [ type            |-> "genesis",
                     prev            |-> NoHash,
                     account         |-> pub,
                     amount          |-> GenesisBalance,
                     recipient       |-> NoHash,
                     source          |-> NoHash,
                     representative |-> NoHash,
                     signature       |-> Sign(priv,
                                            << "genesis", NoHash, pub, GenesisBalance >>) ] IN
        LET h    == CalculateHash(blk, NoHash) IN
        /\ lastHash' = h
        /\ Blocks'   = [Blocks EXCEPT ![h] = blk]
        /\ ledger'   = [n2 \in Node |-> [h2 \in Hash |-> IF h2 = h THEN blk ELSE ledger[n2][h2]]]
        /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
        /\ UNCHANGED << >>

\* Generic block creation (send, open, receive, change)
CreateBlock ==
    /\ lastHash # NoHash
    /\ \E n \in Node :
        LET priv == NodeToKey[n] IN
        LET pub  == PrivateToPublic[priv] IN
        \E btype \in {"send", "open", "receive", "change"} :
            LET blk ==
                [ type            |-> btype,
                  prev            |-> lastHash,
                  account         |-> pub,
                  amount          |-> 0,
                  recipient       |-> NoHash,
                  source          |-> NoHash,
                  representative |-> NoHash,
                  signature       |-> Sign(priv,
                                         << btype, lastHash, pub >>) ] IN
            LET h == CalculateHash(blk, lastHash) IN
            /\ lastHash' = h
            /\ Blocks'   = [Blocks EXCEPT ![h] = blk]
            /\ ledger'   = [n2 \in Node |-> [h2 \in Hash |-> IF h2 = h THEN blk ELSE ledger[n2][h2]]]
            /\ received' = [n2 \in Node |-> received[n2] \cup {h}]
            /\ UNCHANGED << >>

(*--------------------------------------------------------------------
  Processing (validation) of a received block by a node
--------------------------------------------------------------------*)
ProcessBlock ==
    /\ \E n \in Node :
        /\ received[n] # {}
        /\ \E h \in received[n] :
            LET blk == Blocks[h] IN
            /\ blk # NoBlock
            /\ VerifySig(blk.account, blk, blk.signature)
            /\ ledger'   = [n2 \in Node |-> [h2 \in Hash |-> IF h2 = h THEN blk ELSE ledger[n2][h2]]]
            /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] \setminus {h}
                                            ELSE received[n2]]
            /\ UNCHANGED << lastHash, Blocks >>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ CreateGenesis
    \/ CreateBlock
    \/ ProcessBlock

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<lastHash, ledger, received, Blocks>>

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHash
    /\ ledger \in [Node -> [Hash -> (Block \/ NoBlock)]]
    /\ received \in [Node -> SUBSET Hash]
    /\ Blocks \in [Hash -> (Block \/ NoBlock)]

(*--------------------------------------------------------------------
  Safety invariant (all blocks in every ledger have a valid signature)
--------------------------------------------------------------------*)
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == ledger[n][h] IN
            blk # NoBlock => VerifySig(blk.account, blk, blk.signature)

(*--------------------------------------------------------------------
  Operator required by the .cfg substitution
--------------------------------------------------------------------*)
CalculateHashImpl(b, ph) ==
    \* A simple nondeterministic hash generator for model checking
    CHOOSE h \in Hash : TRUE

=============================================================================