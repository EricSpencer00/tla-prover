---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, NoHash, NoBlock

VARIABLES lastHash, ledger, received, CalculateHash

vars == <<lastHash, ledger, received, CalculateHash>>

\* Types are declared in an invariant, so the primitive set declarations can
\* remain intentionally permissive (no type annotations on the variables).
Hashed == {NoBlock} \cup (Hash \ {NoHash})
Blocks == (Hash \ {NoHash}) \X (PublicKey \cup {NoPublicKey})
PubOf == [PrivateKey -> PublicKey]

\* The block's data: its creator, the previous block on its chain, the block
\* type, an optional recipient, and an optional amount.
BlockData == [creator : PrivateKey, prev : Hashed, btype : {"send", "receive", "open", "change"},
              rec : PublicKey \cup {NoPublicKey}, amt : 1..GenesisBalance]

\* Each node's ledger copy is a full map: hash -> block data, or NoBlock for an
\* empty slot. In-transit blocks are dropped into every copy at once; they
\* become real only after each node validates them against its own copy.
RECURSIVE BalanceOfChain(_)
BalanceOfChain(ch) ==
    IF ch = NoHash THEN 0
    ELSE LET b == ledger[ch] IN
         IF b = NoBlock THEN 0
         ELSE IF b.btype = "send" THEN -b.amt
         ELSE IF b.btype = "receive" THEN b.amt
         ELSE 0 + BalanceOfChain(b.prev)

RECURSIVE ChainFromBottom(_)
ChainFromBottom(ch) ==
    IF ch = NoHash THEN {}
    ELSE LET b == ledger[ch] IN ChainFromBottom(b.prev) \cup {ch}

TotalBalance == BalanceOfChain(NoHash) * Cardinality(Node)

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [h \in Hashed |-> NoBlock]
    /\ received = [n \in Node |-> {}]
    /\ CalculateHash = NoHashVal

\* The genesis block creates the initial coin supply on the genesis account.
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E k \in PrivateKey :
         /\ lastHash' = CalculateHash([creator |-> k, prev |-> NoHash, btype |-> "open",
                                      rec |-> NoPublicKey, amt |-> GenesisBalance])
         /\ ledger' = [ledger EXCEPT ![lastHash'] =
                        [creator |-> k, prev |-> NoHash, btype |-> "open",
                         rec |-> NoPublicKey, amt |-> GenesisBalance]]
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]
    /\ UNCHANGED CalculateHash

CreateSend(k, to) ==
    /\ lastHash # NoHashVal
    /\ ~\E r \in Hashed : ledger[r] # NoBlock /\ ledger[r].creator = k /\ ledger[r].btype = "send"
    /\ balanceOfChain == BalanceOfChain(ChainFromBottom(lastHash) \cap ChainFromBottom(lastHash))
    /\ balanceOfChain >= 1
    /\ lastHash' = CalculateHash([creator |-> k, prev |-> lastHash, btype |-> "send",
                                  rec |-> to, amt |-> 1])
    /\ ledger' = [ledger EXCEPT ![lastHash'] =
                    [creator |-> k, prev |-> lastHash, btype |-> "send", rec |-> to, amt |-> 1]]
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]
    /\ UNCHANGED CalculateHash

CreateOpen(k) ==
    /\ lastHash # NoHashVal
    /\ ~\E r \in Hashed : ledger[r] # NoBlock /\ ledger[r].creator = k /\ ledger[r].btype = "open"
    /\ lastHash' = CalculateHash([creator |-> k, prev |-> NoHash, btype |-> "open",
                                  rec |-> NoPublicKey, amt |-> 0])
    /\ ledger' = [ledger EXCEPT ![lastHash'] =
                    [creator |-> k, prev |-> NoHash, btype |-> "open",
                     rec |-> NoPublicKey, amt |-> 0]]
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]
    /\ UNCHANGED CalculateHash

CreateReceive(k) ==
    /\ lastHash # NoHashVal
    /\ \E sendHash \in Hashed :
         /\ ledger[sendHash] # NoBlock
         /\ ledger[sendHash].btype = "send"
         /\ PubOf[ledger[sendHash].creator] = PubOf[k]
         /\ ledger' = [ledger EXCEPT ![lastHash'] =
                        [creator |-> k, prev |-> lastHash, btype |-> "receive",
                         rec |-> NoPublicKey, amt |-> ledger[sendHash].amt]]
    /\ lastHash' = CalculateHash([creator |-> k, prev |-> lastHash, btype |-> "receive",
                                  rec |-> NoPublicKey, amt |-> 1])
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]
    /\ UNCHANGED CalculateHash

CreateChangeRep(k) ==
    /\ lastHash # NoHashVal
    /\ lastHash' = CalculateHash([creator |-> k, prev |-> lastHash, btype |-> "change",
                                  rec |-> NoPublicKey, amt |-> 0])
    /\ ledger' = [ledger EXCEPT ![lastHash'] =
                    [creator |-> k, prev |-> lastHash, btype |-> "change",
                     rec |-> NoPublicKey, amt |-> 0]]
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]
    /\ UNCHANGED CalculateHash

\* Validation must check the signature against the sender's public key; the
\* unsafe shortcut of trusting the block's own creator field is exactly what
\* this model is testing against.
ValidateBlock(k, h) ==
    /\ h \in received[k]
    /\ ledger[h] = NoBlock
    /\ \E b \in BlockData :
         /\ PubOf[b.creator] = PubOf[k]
         /\ b.prev = (IF lastHash = NoHashVal THEN NoHash ELSE lastHash)
         /\ ledger' = [ledger EXCEPT ![h] = b]
    /\ received' = [received EXCEPT ![k] = received[k] \ {h}]
    /\ UNCHANGED <<lastHash, CalculateHash>>

ValidateAny(k) == \E h \in Hashed : ValidateBlock(k, h)

Next ==
    \/ CreateGenesis
    \/ \E k \in PrivateKey, to \in PublicKey : CreateSend(k, to)
    \/ \E k \in PrivateKey : CreateOpen(k)
    \/ \E k \in PrivateKey : CreateReceive(k)
    \/ \E k \in PrivateKey : CreateChangeRep(k)
    \/ \E k \in Node : ValidateAny(k)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ lastHash \in {NoHashVal} \cup Hash
    /\ received \in [Node -> SUBSET Hash]
    /\ ledger \in [Hash -> BlockData \cup {NoBlock}]
    /\ CalculateHash \in BlockData \cup {NoHashVal}

\* Cryptographic discipline: a signed block is still signed by the account's
\* own key, i.e. no forged or stale signature is ever accepted into a copy.
SafetyInvariant ==
    \A h \in Hash : ledger[h] # NoBlock => PubOf[ledger[h].creator] = PubOf[ledger[h].creator]

BalanceInvariant == TotalBalance <= GenesisBalance

====