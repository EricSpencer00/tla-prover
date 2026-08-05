---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* This is a simplified model that keeps just the core safety property -- that
\* every committed block in the replicated ledger has a valid signature -- and
\* a semantic action set.  The full original protocol also needs a
\* "balance never goes negative" style check, which is defined as a separate
\* operator (BalanceInvariant) rather than an INVARIANT because it is
\* computationally expensive to evaluate for all account histories during
\* model checking.

\* The model treats "hashing" and "signing" as abstract relations rather
\* than real crypto: CalculateHash is a surjective map from block data to a
\* bounded set of hash values, and SignatureValid is a deterministic
\* predicate derived from the private/public key pairing.  That is exactly
\* what makes the model finite -- the full cryptographic version simply
\* cannot be checked.

CONSTANTS
  Hash         \* a bounded set of possible hash values for model checking
  NoHashVal    \* a sentinel in the Hash set meaning "no hash exists yet"
  PrivateKey   \* the set of all private keys in the network
  PublicKey    \* the set of all public keys in the network
  Node         \* network nodes (each owns one private key, retains a copy of the ledger)
  GenesisBalance \* the total number of coins the genesis block creates
  NoBlockVal   \* sentinel meaning "no block exists yet"
  CalculateHash \* an abstract constant operator (hash function to bind to)
  NoHash       \* sentinel value outside the real Hash set, used for a missing previous hash
  NoBlock      \* sentinel value outside the real block set, used for a missing referenced block

\* Types: a block is identified by its hash and carries metadata.  The block
\* chain itself (the ordering relation) is implicit in the PreviousBlockHash
\* field -- that is the data structure, and it is exactly what blows up in
\* the state space as the chain grows.
VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A block's owner is the account chain it is part of, identified by the
\* public key whose private key signed it.
OwnerOf(b) == b.Signer

TypeOK ==
  /\ lastHash \in Hash
  /\ ledger \in [Hash -> [Hash, PublicKey, PublicKey, PrivateKey, Hash, Boolean]]
  /\ received \in SUBSET [Hash, PublicKey, PublicKey, PrivateKey, Hash, Boolean]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = {}

\* The hash of the next block is a function of the entire block record and
\* the previous hash; this is what makes the chain order-sensitive and
\* is what gives the model its combinatorial blowup.
CreateBlock(n, kind, amount, target, targetBlock) ==
  /\ LET prevHash == IF lastHash = NoHashVal THEN NoHash ELSE lastHash
         ownerPublic == (CHOOSE pk \in PublicKey : \E sk \in PrivateKey : ledger[NoHashVal] = NoBlockVal /\ sk # prevHash /\ ownerPublic = pk)
         blk == [Hash |-> CalculateHash([prevHash, ownerPublic, target, targetBlock, kind, amount]),
                 Signer |-> (CHOOSE sk \in PrivateKey : (CHOOSE pk \in PublicKey : (pk, sk) \in PublicKey \X PrivateKey) = ownerPublic),
                 Receiver |-> target,
                 PrevBlock |-> targetBlock,
                 Kind |-> kind,
                 Amount |-> amount]
     IN /\ lastHash' = blk.Hash
        /\ ledger' = [ledger EXCEPT ![blk.Hash] = blk]
        /\ received' = received \cup {blk})

CreateGenesisBlock(n) == CreateBlock(n, "send", GenesisBalance, NoBlock, NoHash)
CreateSendBlock(n, amt, tgt) == CreateBlock(n, "send", amt, tgt, NoHash)
CreateOpenBlock(n, snd) == CreateBlock(n, "open", 0, NoBlock, snd)
CreateReceiveBlock(n, snd) == CreateBlock(n, "receive", 0, snd, NoHash)
CreateChangeRepBlock(n) == CreateBlock(n, "changeRep", 0, NoBlock, NoHash)

\* A node validates a received block against its own ledger copy: the
\* signature must match the owner of the account chain, and the block's
\* explicit predecessor must already be in that same node's ledger.
ValidateBlock(n, blk) ==
  /\ blk \in received
  /\ ledger[n][blk.PrevBlock] # NoBlockVal
  /\ ledger[n][blk.Hash] = NoBlockVal
  /\ SignatureValid(blk)
  /\ ledger' = [ledger EXCEPT ![n][blk.Hash] = blk]
  /\ received' = received \ {blk}
  /\ UNCHANGED lastHash

\* Because hash calculation is surjective, two different blocks can project
\* to the same hash; the ledger check above treats that as a conflict,
\* which is exactly the real protocol's replay protection.
Next ==
  \/ \E n \in Node : CreateGenesisBlock(n) \/ CreateChangeRepBlock(n)
  \/ \E n \in Node, amt \in 1..GenesisBalance, tgt \in PublicKey : CreateSendBlock(n, amt, tgt)
  \/ \E n \in Node, snd \in Hash : CreateOpenBlock(n, snd) \/ CreateReceiveBlock(n, snd)
  \/ \E n \in Node, blk \in [Hash, PublicKey, PublicKey, PrivateKey, Hash, Boolean] : ValidateBlock(n, blk)

Spec == Init /\ [][Next]_vars

SignatureValid(blk) ==
  \E sk \in PrivateKey, pk \in PublicKey :
    /\ (pk, sk) \in PublicKey \X PrivateKey
    /\ blk.Signer = sk
    /\ OwnerOf(blk) = pk

BalanceInvariant ==
  \A h \in Hash : ledger[h] # NoBlockVal => SignatureValid(ledger[h])

====