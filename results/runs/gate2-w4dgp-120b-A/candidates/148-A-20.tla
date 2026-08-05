---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* The ownership relation is a simple function because each node has one key.
OwnerOf(p) == CHOOSE n \in Node : p \in OwnerKey[n]

\* Recursive balance walk: each account chain is exactly a sequence of blocks.
RECURSIVE BalanceSeq(_)
BalanceSeq(s) ==
  IF s = <<>> THEN 0
  ELSE (IF Head(s).type = "send" THEN 0 ELSE Head(s).amount) + BalanceSeq(Tail(s))

BalanaceOfChain(account) == BalanceSeq(ChainFor(account))

\* The full chain for an account is built by walking back through prevBlock.
RECURSIVE ChainFor(_)
ChainFor(account) == ChainForAt(account, ledger[account][NoHash])

ChainForAt(account, hb) ==
  IF hb = NoHash THEN <<>>
  ELSE
    LET prev == ledger[account][hb]
        rest == ChainForAt(account, prev.prevOfChain)
    IN IF rest = <<>> THEN <<prev>>
       ELSE CHOOSE c \in (rest \cup {prev}) : \A b \in (rest \cup {prev}) : b.prevOfChain <= c.prevOfChain

RECURSIVE ChainForHash(_)
ChainForHash(h) ==
  IF h = NoHash THEN <<>>
  ELSE LET b == ledger[OwnerOf(h)][h] IN IF b.prevOfChain = NoHash THEN <<b>>
       ELSE LET prevc == ChainForHash(b.prevOfChain) IN IF prevc = <<>> THEN <<b>> ELSE prevc \cup {b}

RECURSIVE BalanceSeqHash(_)
BalanceSeqHash(hs) ==
  IF hs = <<>> THEN 0
  ELSE IF Head(hs).type = "send" THEN 0 ELSE Head(hs).amount + BalanceSeqHash(Tail(hs))

BalanceOfChainHash(account) == BalanceSeqHash(ChainForHash(ledger[account][NoHash]))

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n, p) ==
  /\ ledger[OwnerOf(p)][NoHash] = NoBlockVal
  /\ ledger[OwnerOf(p)][NoHash] =
       [prevOfChain |-> NoHash, type |-> "open", from |-> NoHash, to |-> OwnerOf(p), amount |-> GenesisBalance,
         signature |-> Ed25519.Sign(p, LastHash), pubKey |-> OwnerOf(p)]
  /\ lastHash' = NoHash
  /\ received' = [m \in Node |-> {NoHash}]
  /\ UNCHANGED ledger

\* New block hashes are calculated externally, not built from the chain itself.
CreateSendBlock(n, p, to, amt, nh) ==
  /\ nh \notin ledger[OwnerOf(p)]
  /\ ledger[OwnerOf(p)][NoHash].type \in {"open", "receive", "change"}
  /\ BalanceOfChainHash(OwnerOf(p)) >= amt
  /\ ledger' = [ledger EXCEPT ![OwnerOf(p)][nh] =
        [prevOfChain |-> lastHash, type |-> "send", from |-> OwnerOf(p), to |-> to, amount |-> amt,
         signature |-> Ed25519.Sign(p, nh), pubKey |-> OwnerOf(p)]]
  /\ lastHash' = nh
  /\ received' = [m \in Node |-> received[m] \cup {nh}]
  /\ UNCHANGED <<>>

CreateOpenBlock(n, p, h, nh) ==
  /\ ledger[OwnerOf(p)][NoHash].type = "null"
  /\ h \in ledger[OwnerOf(p)]
  /\ ledger[OwnerOf(p)][h].type = "send"
  /\ ledger[OwnerOf(p)][h].to = OwnerOf(p)
  /\ nh \notin ledger[OwnerOf(p)]
  /\ ledger' = [ledger EXCEPT ![OwnerOf(p)][nh] =
        [prevOfChain |-> NoHash, type |-> "open", from |-> NoHash, to |-> OwnerOf(p), amount |-> ledger[OwnerOf(p)][h].amount,
         signature |-> Ed25519.Sign(p, nh), pubKey |-> OwnerOf(p)]]
  /\ lastHash' = nh
  /\ received' = [m \in Node |-> received[m] \cup {nh}]
  /\ UNCHANGED <<>>

CreateReceiveBlock(n, p, h, nh) ==
  /\ h \in ledger[OwnerOf(p)]
  /\ ledger[OwnerOf(p)][h].type = "send"
  /\ ledger[OwnerOf(p)][h].to = OwnerOf(p)
  /\ ledger' = [ledger EXCEPT ![OwnerOf(p)][nh] =
        [prevOfChain |-> lastHash, type |-> "receive", from |-> h, to |-> OwnerOf(p), amount |-> 0,
         signature |-> Ed25519.Sign(p, nh), pubKey |-> OwnerOf(p)]]
  /\ lastHash' = nh
  /\ received' = [m \in Node |-> received[m] \cup {nh}]
  /\ UNCHANGED <<>>

CreateChangeBlock(n, p, nh) ==
  /\ ledger[OwnerOf(p)][NoHash].type \in {"open", "receive", "change"}
  /\ nh \notin ledger[OwnerOf(p)]
  /\ ledger' = [ledger EXCEPT ![OwnerOf(p)][nh] =
        [prevOfChain |-> lastHash, type |-> "change", from |-> NoHash, to |-> OwnerOf(p), amount |-> 0,
         signature |-> Ed25519.Sign(p, nh), pubKey |-> OwnerOf(p)]]
  /\ lastHash' = nh
  /\ received' = [m \in Node |-> received[m] \cup {nh}]
  /\ UNCHANGED <<>>

Next == \E n \in Node, p \in PrivateKey, to \in Node, amt \in {1}, nh \in Hash :
           \/ CreateGenesisBlock(n, p)
           \/ CreateSendBlock(n, p, to, amt, nh)
           \/ CreateOpenBlock(n, p, nh, nh)
           \/ CreateReceiveBlock(n, p, nh, nh)
           \/ CreateChangeBlock(n, p, nh)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> [prevOfChain: Hash \cup {NoHash}, type: {"null", "open", "send", "receive", "change"},
                     from: Node \cup {NoHash}, to: Node \cup {NoHash}, amount: {0, 1},
                     signature: {NoBlockVal} \cup (PublicKey \X Hash), pubKey: PublicKey \cup {NoHash}]]]
  /\ received \in [Node -> SUBSET Hash]

\* Safety invariant: every block in every copy of the ledger has a valid signature
\* (the copy check rather than a single shared copy checks that a node does not
\* accept a block on the strength of another node's verification).
SafetyInvariant ==
  \A n \in Node, h \in Hash :
    ledger[n][h] # NoBlockVal => Ed25519.ValidSignature(ledger[n][h].pubKey, h, ledger[n][h].signature)

====