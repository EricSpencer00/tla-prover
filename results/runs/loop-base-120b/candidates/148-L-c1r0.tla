---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants required by the .cfg file
--------------------------------------------------------------------*)
CONSTANTS
    Hash,           \* set of possible block hashes
    NoHash,         \* sentinel hash meaning "no previous hash"
    NoHashVal,      \* (unused sentinel value, kept for compatibility)
    PrivateKey,    \* set of private keys
    PublicKey,     \* set of public keys
    Node,          \* set of network nodes
    GenesisBalance,\* total coin supply at genesis
    NoBlock,       \* sentinel value meaning "no block stored"
    NoBlockVal,    \* (unused sentinel value, kept for compatibility)
    CalculateHash, \* abstract hash operator (overridden in the cfg)
    CalculateHashImpl

(*--------------------------------------------------------------------
  Types used in the specification
--------------------------------------------------------------------*)
BlockType == {"Genesis", "Send", "Receive", "Open", "Change"}

Sig == {"sig1", "sig2", "sig3"} \* abstract signature values

Block == [
    type      : BlockType,
    prev      : Hash,
    account   : PublicKey,
    amount    : Nat,
    recipient : PublicKey,
    rep       : PublicKey,
    sig       : Sig
]

BlockOrNone == Block \cup {NoBlock}

(*--------------------------------------------------------------------
  Cryptographic primitives (abstract)
--------------------------------------------------------------------*)
Sign(priv, data) == CHOOSE s \in Sig : TRUE

Verify(sig, data, pub) == TRUE \* abstract verification, assumed correct

ValidSignature(b) == Verify(b.sig, b, b.account)

(*--------------------------------------------------------------------
  Mapping from private keys to public keys and ownership of keys
--------------------------------------------------------------------*)
PrivateToPublic \in [PrivateKey -> PublicKey]
NodePriv          \in [Node -> PrivateKey]

(*--------------------------------------------------------------------
  Helper constants
--------------------------------------------------------------------*)
SomeNode == CHOOSE n \in Node : TRUE
GenesisAccount == CHOOSE pk \in PublicKey : TRUE

(*--------------------------------------------------------------------
  Hash calculation (abstract, overridden by the configuration)
--------------------------------------------------------------------*)
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

(* Default (nondeterministic) implementation; the .cfg file will replace it *)
CalculateHashImpl(data, prev) == CHOOSE h \in Hash : TRUE

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    lastHash,   \* the hash of the most recently created block
    ledger,     \* per‑node copy of the ledger: [Node -> [Hash -> BlockOrNone]]
    received    \* per‑node set of hashes that have been received but not yet processed

vars == << lastHash, ledger, received >>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E pk \in PublicKey :
        LET blk == [
                type      |-> "Genesis",
                prev      |-> NoHash,
                account   |-> pk,
                amount    |-> GenesisBalance,
                recipient |-> pk,
                rep       |-> pk,
                sig       |-> Sign(NodePriv[SomeNode], "genesis")
            ] IN
        /\ newHash = CalculateHash(blk, lastHash)
        /\ newHash # NoHash
        /\ lastHash' = newHash
        /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = newHash THEN blk ELSE ledger[n][h]]]
        /\ received' = [n \in Node |-> received[n] \cup {newHash}]
    /\ UNCHANGED << >>

CreateBlock ==
    /\ lastHash # NoHash
    /\ \E typ \in BlockType,
          acct \in PublicKey,
          amt  \in Nat,
          recp \in PublicKey,
          rp   \in PublicKey :
        LET blk == [
                type      |-> typ,
                prev      |-> lastHash,
                account   |-> acct,
                amount    |-> amt,
                recipient |-> recp,
                rep       |-> rp,
                sig       |-> Sign(NodePriv[SomeNode], "data")
            ] IN
        /\ newHash = CalculateHash(blk, lastHash)
        /\ newHash # NoHash
        /\ lastHash' = newHash
        /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = newHash THEN blk ELSE ledger[n][h]]]
        /\ received' = [n \in Node |-> received[n] \cup {newHash}]
    /\ UNCHANGED << >>

ProcessReceived ==
    /\ \E n \in Node, h \in received[n] :
        /\ received' = [m \in Node |-> IF m = n THEN received[m] \ {h} ELSE received[m]]
        /\ UNCHANGED << lastHash, ledger >>
    /\ UNCHANGED << >>

Next ==
    \/ CreateGenesis
    \/ CreateBlock
    \/ ProcessReceived

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> BlockOrNone]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            (ledger[n][h] # NoBlock) => ValidSignature(ledger[n][h])

====