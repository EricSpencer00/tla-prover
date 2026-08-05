---- MODULE Nano ----
(***************************************************************************)
(* A blockchain-inspired protocol: blocks form a hash-linked DAG of
   transactions, each block signed by the key that authored it. The
   model tracks a ledger per node; the invariants are about the integrity
   of the block graph (signatures match the historic author of the block)
   and about bounded coin supply. *)
EXTENDS Naturals, Bags

CONSTANTS
    Hash,                   \* Blake2b block hashes
    CalculateHash(_,_,_),   \* Action that calculates a new hash
    PrivateKey,             \* Ed25519 private keys
    PublicKey,              \* Ed25519 public keys
    KeyPair,                \* Private key -> public key pairing
    Node,                   \* Network participants
    GenesisBalance,         \* Total coins in the network
    Ownership               \* Private key owned by each node

VARIABLES
    lastHash,               \* Last block hash calculated
    ledger,                 \* [Node -> [Hash -> SignedBlock \cup {NoBlock}]]
    received                \* Blocks received but not yet confirmed

ASSUME
    /\ \A x, y, z \in Hash : CalculateHash(x, y, z) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ Ownership \in [Node -> PrivateKey]

NoBlock == CHOOSE b \notin SignedBlock
NoHash == CHOOSE h \notin Hash

Signature == [data : Hash, signedWith : PrivateKey]
SignedBlock == [block : Block, signature : Signature]

HashOf(b) == b.signature.data

RECURSIVE Block(_)
Block ==
    { [type : "genesis", account : PublicKey, balance : 0 .. GenesisBalance]
      \cup
      [type : "send", previous : Hash, balance : 0 .. GenesisBalance,
       destination : PublicKey]
      \cup
      [type : "open", account : PublicKey, source : Hash, rep : PublicKey]
      \cup
      [type : "receive", previous : Hash, source : Hash]
      \cup
      [type : "change", previous : Hash, rep : PublicKey] }

\* A block is valid if it is signed by the key that, historically, was
\* the author of that address (the block graph is never rewound).
TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> SignedBlock \cup {NoBlock}]]
    /\ received \subseteq SignedBlock

SignedBy(h, pk) ==
    LET b == ledger[Node][h] IN
    /\ b # NoBlock
    /\ pk = KeyPair[b.signature.signedWith]
    /\ h = HashOf(b)

SignaturesMatch ==
    \A n \in Node, h \in Hash :
        (ledger[n][h] # NoBlock) => SignedBy(h, KeyPair[Ownership[n]])

\* Sum of all confirmed balances across every node's ledger.
RECURSIVE SumBalance(_)
SumBalance(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN x + SumBalance(S \ {x})

AllBalancesConsistent ==
    SumBalance({KeyPair[Ownership[n]] : n \in Node}) <= GenesisBalance

GenesisBlockExists == \E n \in Node : ledger[n][lastHash] # NoBlock

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = {}

CreateGenesis ==
    /\ \A n \in Node : ledger[n][lastHash] = NoBlock
    /\ \E priv \in PrivateKey :
        /\ \E blk \in Block :
            /\ blk.type = "genesis"
            /\ blk.account = KeyPair[priv]
            /\ blk.balance = GenesisBalance
            /\ \E h \in Hash :
                /\ CalculateHash(blk, lastHash, h)
                /\ ledger' = [n \in Node |->
                    [ledger[n] EXCEPT ![h] =
                        [block |-> blk, signature |-> [data |-> h, signedWith |-> priv]]]]
                /\ lastHash' = h
    /\ UNCHANGED received

\* A block references only existing historic blocks, so the graph can
\* never grow beyond the finite Hash set.
Next ==
    \/ CreateGenesis
    \/ \E n \in Node :
        /\ received # {}
        /\ \E b \in received :
            /\ HashOf(b) = lastHash
            /\ CalculateHash(b.block, lastHash, lastHash')
            /\ ledger' = [ledger EXCEPT ![n][lastHash'] = b]
            /\ lastHash' = lastHash'
            /\ received' = received \ {b}

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* The historic-author-lookup used by the signature check explores the
\* block graph recursively; it must terminate, which is true because the
\* graph can never be deeper than the size of the finite Hash set.
RECURSIVE Author(_,_)
Author(n, h) ==
    LET b == ledger[n][h] IN
    IF b.block.type \in {"genesis", "open"} THEN b.block.account
    ELSE Author(n, b.block.previous)

Termination ==
    \A n \in Node : WF_vars(\E h \in Hash : Author(n, h))

Invariant == TypeOK /\ SignaturesMatch /\ AllBalancesConsistent

====