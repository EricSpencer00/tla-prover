---- MODULE Nano ----
(***************************************************************************)
(* An outdated and not-ultimately-useful specification of the original     *)
(* protocol used by the Nano blockchain. Primarily interesting as an       *)
(* example of how to model hash functions and cryptographic signatures,    *)
(* and the difficulties in using finite modelchecking to analyze           *)
(* blockchain-like data structures, or anything that records action         *)
(* history in an ordered way.                                              *)
(***************************************************************************)

EXTENDS Naturals, Bags

CONSTANTS
    Hash,                   \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* An action calculating the hash of a block
    PrivateKey,             \* The set of all Ed25519 private keys
    PublicKey,              \* The set of all Ed25519 public keys
    KeyPair,                \* The public key paired with each private key
    Node,                   \* The set of all nodes in the network
    GenesisBalance,         \* The total number of coins in the network
    Ownership               \* The private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

(***************************************************************************)
(* Functions to sign hashes with private key and validate signatures       *)
(* against public key.                                                     *)
(***************************************************************************)

SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature ==
    [data : Hash, signedWith : PrivateKey]

(***************************************************************************)
(* Defines the set of protocol-conforming blocks.                          *)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type |-> "genesis", account |-> CHOOSE p \in PublicKey : TRUE, balance |-> GenesisBalance]

SendBlock ==
    [previous : Hash, balance : AccountBalance, destination : PublicKey, type |-> "send"]

OpenBlock ==
    [account : PublicKey, source : Hash, rep : PublicKey, type |-> "open"]

ReceiveBlock ==
    [previous : Hash, source : Hash, type |-> "receive"]

ChangeRepBlock ==
    [previous : Hash, rep : PublicKey, type |-> "change"]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b \in SignedBlock : FALSE

NoHash == CHOOSE h \in Hash : FALSE

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(***************************************************************************)
(* Utility functions to calculate block lattice properties.                *)
(***************************************************************************)

GenesisBlockExists == lastHash /= NoHash

IsAccountOpen(ledger, publicKey) ==
    \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock # NoBlock
        /\ signedBlock.block.type \in {"genesis", "open"}
        /\ signedBlock.block.account = publicKey

IsSendReceived(ledger, sourceHash) ==
    \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        signedBlock # NoBlock
        /\ signedBlock.block.type \in {"open", "receive"}
        /\ signedBlock.block.source = sourceHash

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, blockHash) ==
    LET sb == ledger[blockHash] IN
    IF sb.block.type \in {"genesis", "open"}
    THEN sb.block.account
    ELSE PublicKeyOf(ledger, sb.block.previous)

TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET sb == ledger[hash] IN
        sb # NoBlock
        /\ PublicKeyOf(ledger, hash) = publicKey
        /\ ~\E oh \in Hash :
            LET osb == ledger[oh] IN
            osb # NoBlock
            /\ osb.block.type \in {"send", "receive", "change"}
            /\ osb.block.previous = hash

RECURSIVE BalanceAt(_, _)
RECURSIVE ValueOfSendBlock(_, _)

BalanceAt(ledger, hash) ==
    LET block == ledger[hash].block IN
    CASE block.type = "open" -> ValueOfSendBlock(ledger, block.source)
      [] block.type = "send" -> block.balance
      [] block.type = "receive" ->
            BalanceAt(ledger, block.previous) + ValueOfSendBlock(ledger, block.source)
      [] block.type = "change" -> BalanceAt(ledger, block.previous)
      [] block.type = "genesis" -> block.balance

ValueOfSendBlock(ledger, hash) ==
    BalanceAt(ledger, ledger[hash].block.previous) - ledger[hash].block.balance

(***************************************************************************)
(* The type & safety invariants.                                           *)
(***************************************************************************)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    \A node \in Node :
        LET ledger == distributedLedger[node] IN
        \A hash \in Hash :
            LET sb == ledger[hash] IN
            sb # NoBlock =>
                LET publicKey == PublicKeyOf(ledger, hash) IN
                ValidateSignature(sb.signature, publicKey, hash)

SafetyInvariant == CryptographicInvariant

BalanceInvariant ==
    \A node \in Node :
        LET ledger == distributedLedger[node] IN
        LET openAccounts == {a \in PublicKey : IsAccountOpen(ledger, a)} IN
        LET topBlocks == {TopBlock(ledger, a) : a \in openAccounts} IN
        LET accountBalances ==
            LET f(hash) == BalanceAt(ledger, hash) IN BagOfAll(f, SetToBag(topBlocks)) IN
        IF GenesisBlockExists THEN SumBag(accountBalances) <= GenesisBalance

=============================================================================