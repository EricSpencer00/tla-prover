---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,                   \* Set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* Action calculating the hash of a block
    PrivateKey,             \* Set of all Ed25519 private keys
    PublicKey,              \* Set of all Ed25519 public keys
    KeyPair,                \* The public key paired with each private key
    Node,                   \* Set of all network nodes
    GenesisBalance,         \* Total number of coins in the network
    Ownership               \* The private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    ledger,                 \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

ASSUME /\ \A data, oldHash, newHash :
            CalculateHash(data, oldHash, newHash) \in BOOLEAN
       /\ KeyPair \in [PrivateKey -> PublicKey]
       /\ GenesisBalance \in Nat
       /\ Ownership \in [Node -> PrivateKey]

\* Sign a hash with a private key.
SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

\* Validate a signature against a public key.
ValidateSignature(sig, expectedKey, expectedHash) ==
    /\ KeyPair[sig.signedWith] = expectedKey
    /\ sig.data = expectedHash

Signature == [data : Hash, signedWith : PrivateKey]

GenesisBlock ==
    [type |-> "genesis", account |-> "GAccount", balance |-> GenesisBalance]

SendBlock ==
    [previous : Hash, balance : 0 .. GenesisBalance,
     destination : PublicKey, type |-> "send"]

OpenBlock ==
    [account : PublicKey, source : Hash,
     rep : PublicKey, type |-> "open"]

ReceiveBlock ==
    [previous : Hash, source : Hash, type |-> "receive"]

ChangeBlock ==
    [previous : Hash, rep : PublicKey, type |-> "change"]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeBlock

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b \in Block : b.type = "send"
NoHash == CHOOSE h \in Hash : h # h

\* The ledger maps hashes to signed blocks, with NoBlock as a placeholder.
Ledger == [Hash -> SignedBlock \cup {NoBlock}]

TypeInv ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

\* No block is ever written without a signature validated cryptographically.
SafetyInv ==
    \A n \in Node :
        \A h \in Hash :
            (ledger[n][h] # NoBlock)
                => ValidateSignature(ledger[n][h].signature,
                                      ledger[n][h].block.account, h)

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* Genesis block: written directly, never re-validated.
CreateGenesisBlock(priv) ==
    /\ lastHash = NoHash
    /\ CalculateHash(GenesisBlock, lastHash, lastHash')
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] =
                        [block |-> GenesisBlock,
                         signature |-> SignHash(lastHash', priv)]]]
    /\ UNCHANGED <<lastHash, received>>

CreateSend(n) ==
    /\ \E prev \in Hash :
        /\ ledger[n][prev] # NoBlock
        /\ \E dst \in PublicKey, bal \in 0 .. GenesisBalance :
            /\ bal < GenesisBalance
            /\ CalculateHash([previous |-> prev, balance |-> bal,
                              destination |-> dst, type |-> "send"],
                             lastHash, lastHash')
            /\ received' = [received EXCEPT ![n] =
                    @ \cup {[block |-> [previous |-> prev, balance |-> bal,
                                      destination |-> dst, type |-> "send"],
                              signature |-> SignHash(lastHash', Ownership[n])]}]
    /\ UNCHANGED <<lastHash, ledger>>

ConfirmSend(n, b) ==
    /\ b \in received[n]
    /\ b.block.type = "send"
    /\ CalculateHash(b.block, lastHash, lastHash')
    /\ ValidateSignature(b.signature,
                         KeyPair[Ownership[n]], lastHash')
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = b]
    /\ received' = [received EXCEPT ![n] = @ \ {b}]
    /\ UNCHANGED <<lastHash>>

Next ==
    \/ \E priv \in PrivateKey : CreateGenesisBlock(priv)
    \/ \E n \in Node : CreateSend(n)
    \/ \E n \in Node, b \in SignedBlock : ConfirmSend(n, b)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

THEOREM TypeInv /\ SafetyInv

====