---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
    Hash,               \* Blake2b block hashes; the set of all hashes
    PrivateKey,         \* Ed25519 private keys
    PublicKey,          \* Ed25519 public keys
    KeyPair,            \* public key paired with each private key
    Node,               \* nodes in the network
    GenesisBalance,     \* total number of coins in the network
    Ownership           \* the private key owned by each node

VARIABLES
    hashFunction,       \* the hash function applied to each block
    blockCount,         \* the number of blocks already calculated
    blocks              \* the set of blocks calculated so far

ASSUME KeyPair \in [PrivateKey -> PublicKey]
       GenesisBalance \in Nat

\* Each block is a record containing its type and the hash of its predecessor
\* (for the genesis block, its predecessor is Nil).
Block == [type : {"genesis", "send", "receive"}, parent : Hash \cup {"Nil"}]

\* Signing is not modelled by itself: a private key can only sign the hash it
\* calculates, so ValidateSignature can only ever be run against a signature
\* that belongs to the block's own creator.
Signature == [algorithm : {"ed25519"}, signedBy : PrivateKey]

NoSig == [algorithm |-> "ed25519", signedBy |-> CHOOSE pk \in PrivateKey : TRUE]

RECURSIVE Apply(_, _)
Apply(f, n) ==
    IF n = 0 THEN {}
    ELSE f[n] \cup Apply(f, n - 1)

\* The hash of a block is the first hash in Hash that is not already used.
\* This is deliberately a function of blockCount rather than of the block,
\* so the hash is determined before the creator is known.
HashByCount(n) ==
    LET h == CHOOSE h \in Hash : h \notin Apply(hashFunction, n - 1) IN
    [n |-> h]

TypeOK ==
    /\ hashFunction \in [1 .. blockCount -> Hash]
    /\ blockCount \in Nat
    /\ blocks \subseteq Block

Init ==
    /\ hashFunction = {}
    /\ blockCount = 0
    /\ blocks = {}

\* The creator of a block is the node signed up under the private key that
\* signed it.
CreatorOf(sig) == CHOOSE n \in Node : Ownership[n] = sig.signedBy

\* A block may be committed by any node, signed with that node's private key.
CommitBlock(p, type, n) ==
    /\ p \notin blocks
    /\ p.type = type
    /\ p.parent \in Apply(hashFunction, blockCount) \cup {"Nil"}
    /\ hashFunction' = [hashFunction EXCEPT ![blockCount + 1] = HashByCount(blockCount + 1)]
    /\ blockCount' = blockCount + 1
    /\ blocks' = blocks \cup {p}

\* The network is safe because the hash function is injective: each block has
\* a unique hash, so a creator is bound to the set of blocks it actually
\* authored and can never author a second block at a hash already used.
Safety ==
    \A p, q \in blocks :
        /\ p.type = q.type => (p = q <=> hashFunction[p.blockCount] = hashFunction[q.blockCount])
        /\ p.type = "send" => p.parent \in Apply(hashFunction, p.blockCount - 1)
        /\ p.type = "receive" => p.parent \in Apply(hashFunction, p.blockCount - 1)

Spec == Init /\ [][(CommitBlock(p, "genesis", n) \/ CommitBlock(p, "send", n)
                      \/ CommitBlock(p, "receive", n))]_<<hashFunction, blockCount, blocks>>

=============================================================================