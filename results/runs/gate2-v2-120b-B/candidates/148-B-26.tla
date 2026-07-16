---- MODULE Nano ----
(***************************************************************************)
(* An outdated and not-ultimately-useful specification of the original     *)
(* protocol used by the Nano blockchain. Primarily interesting as an       *)
(* example of how to model hash functions and cryptographic signatures,    *)
(* and the difficulties in using finite modelchecking to analyze           *)
(* blockchain-like data structures or anything else that records action    *)
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
    lastHash,               \* The last calculated block hash (or NoHash)
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash :
        CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

(***************************************************************************)
(* Functions to sign hashes with a private key and validate signatures    *)
(* against a public key.                                                   *)
(***************************************************************************)

Signature == [data : Hash, signedWith : PrivateKey]

SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(sig, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[sig.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ sig.data = expectedHash

(***************************************************************************)
(* Block definitions                                                       *)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type |-> "genesis",
     account |-> PublicKey,
     balance |-> GenesisBalance]

SendBlock ==
    [type |-> "send",
     previous |-> Hash,
     balance |-> AccountBalance,
     destination |-> PublicKey]

OpenBlock ==
    [type |-> "open",
     account |-> PublicKey,
     source |-> Hash,
     rep |-> PublicKey]

ReceiveBlock ==
    [type |-> "receive",
     previous |-> Hash,
     source |-> Hash]

ChangeRepBlock ==
    [type |-> "change",
     previous |-> Hash,
     rep |-> PublicKey]

Block ==
    GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b \in Block : b \notin SignedBlock
NoHash  == CHOOSE h \in Hash  : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(***************************************************************************)
(* Utility functions                                                       *)
(***************************************************************************)

GenesisBlockExists ==
    lastHash /= NoHash

IsAccountOpen(ledger, acc) ==
    \E h \in Hash :
        LET sb == ledger[h] IN
        sb /= NoBlock /\ sb.block.type \in {"genesis", "open"} /\ sb.block.account = acc

IsSendReceived(ledger, src) ==
    \E h \in Hash :
        LET sb == ledger[h] IN
        sb /= NoBlock /\ sb.block.type \in {"open", "receive"} /\ sb.block.source = src

RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, h) ==
    LET sb == ledger[h] IN
    LET blk == sb.block IN
    IF blk.type \in {"genesis", "open"}
       THEN blk.account
       ELSE PublicKeyOf(ledger, blk.previous)

RECURSIVE BalanceAt(_,_)
BalanceAt(ledger, h) ==
    LET sb == ledger[h] IN
    LET blk == sb.block IN
    CASE blk.type = "open"   -> ValueOfSendBlock(ledger, blk.source)
    []   blk.type = "send"   -> blk.balance
    []   blk.type = "receive"-> BalanceAt(ledger, blk.previous) +
                               ValueOfSendBlock(ledger, blk.source)
    []   blk.type = "change" -> BalanceAt(ledger, blk.previous)
    []   blk.type = "genesis"-> blk.balance

RECURSIVE ValueOfSendBlock(_,_)
ValueOfSendBlock(ledger, h) ==
    LET sb == ledger[h] IN
    LET blk == sb.block IN
    BalanceAt(ledger, blk.previous) - blk.balance

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE LET e \in S : e + SumBag(B \ {e})

(***************************************************************************)
(* Invariants                                                               *)
(***************************************************************************)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A n \in Node :
        LET ledger == distributedLedger[n] IN
        \A h \in Hash :
            LET sb == ledger[h] IN
            sb /= NoBlock =>
                LET pk == PublicKeyOf(ledger, h) IN
                ValidateSignature(sb.signature, pk, h)

BalanceInvariant ==
    /\ \A n \in Node :
        LET ledger == distributedLedger[n] IN
        LET openAccs == {a \in PublicKey : IsAccountOpen(ledger, a)} IN
        LET tops == {PublicKeyOf(ledger, h) = a : a \in openAccs} IN
        (* The concrete definition of top blocks is cumbersome; we conservatively *)
        (* bound the sum of all balances by GenesisBalance.                     *)
        SumBag({BalanceAt(ledger, h) : h \in Hash /\ ledger[h] /= NoBlock}) <= GenesisBalance

SafetyInvariant == CryptographicInvariant

=============================================================================