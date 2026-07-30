---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node,
  GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* The content of a block is the stuff the hash operator hashes over: the
\* account chain it belongs to, the hash it directly follows, the block type,
\* and whatever parameters the type carries (amount, recipient, previous
\* sender block, or new rep). The operator is abstract and supplied by the
\* model checker.
BlockContent(a, ph, t, u) == "a" \in a /\ "p" \in ph /\ "t" \in t /\ "u" \in u

\* A signed block is the content plus a signature derived from the account's
\* private key (the Ed25519 model). Sign is a simple injection here.
SignedBlock(a, ph, t, u, sk) == [blk |-> BlockContent(a, ph, t, u), sig |-> sk]

\* A node's local copy of the distributed ledger maps block hashes to signed
\* blocks (or a sentinel) and its own inbox holds received blocks.
AtNode(n) == [hash |-> ledger[n][hash]]
Inbox(n) == [hash |-> received[n][hash]]

\* Balance walks an account chain backwards from the last hash, counting the
\* value of every block that belongs to that account.
RECURSIVE Summarize(_)
Summarize(h) ==
  IF h = NoHashVal
  THEN 0
  ELSE
    LET b == AtNode(Node)[h] IN
      IF b = NoBlockVal
      THEN 0
      ELSE LET suffix == Summarize(b.blk.p) IN
        IF b.blk.t = "send" /\ b.blk.a = a
        THEN suffix - b.blk.u
        ELSE IF b.blk.t = "receive" /\ b.blk.a = a
        THEN suffix + b.blk.u
        ELSE suffix

RECURSIVE ClaimedBy(_)
ClaimedBy(h) ==
  IF h = NoHashVal
  THEN {}
  ELSE
    LET b == AtNode(Node)[h] IN
      IF b = NoBlockVal
      THEN {}
      ELSE IF b.blk.t \in {"send", "receive"}
      THEN {b.blk.u} \cup ClaimedBy(b.blk.p)
      ELSE ClaimedBy(b.blk.p)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [hash \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> [hash \in Hash |-> NoBlockVal]]

\* The genesis block is broadcast to all nodes' inboxes and written into every
\* node's copy of the ledger at the same moment (no reordering of the first
\* block is possible).
CreateGenesisBlock(sk) ==
  /\ lastHash = NoHashVal
  /\ LET nh == CalculateHash(BlockContent(Node, NoHashVal, "genesis", GenesisBalance), NoHashVal) IN
     /\ lastHash' = nh
     /\ ledger' = [n \in Node |-> [hash |-> IF hash = nh THEN SignedBlock(Node, NoHashVal, "genesis", GenesisBalance, sk) ELSE NoBlockVal]]
     /\ received' = [n \in Node |-> [hash |-> IF hash = nh THEN SignedBlock(Node, NoHashVal, "genesis", GenesisBalance, sk) ELSE NoBlockVal]]

CreateSendBlock(a, sk, b, amt) ==
  /\ lastHash # NoHashVal
  /\ Summarize(lastHash) >= amt
  /\ LET nh == CalculateHash(BlockContent(a, lastHash, "send", amt), lastHash) IN
     /\ lastHash' = nh
     /\ ledger' = [ledger EXCEPT ![Node] = [hash |-> IF hash = nh THEN SignedBlock(a, lastHash, "send", amt, sk) ELSE @]]
     /\ received' = [n \in Node |-> [hash |-> IF hash = nh THEN SignedBlock(a, lastHash, "send", amt, sk) ELSE @]]

CreateOpenBlock(a, sk, src) ==
  /\ lastHash # NoHashVal
  /\ ~ \E h \in Hash : AtNode(Node)[h] # NoBlockVal /\ AtNode(Node)[h].blk.t = "open" /\ AtNode(Node)[h].blk.u = src
  /\ LET nh == CalculateHash(BlockContent(a, src, "open", 0), noHash) IN
     /\ lastHash' = nh
     /\ ledger' = [Node |-> [hash |-> IF hash = nh THEN SignedBlock(a, src, "open", 0, sk) ELSE ledger[Node][hash]]]
     /\ received' = [n \in Node |-> [hash |-> IF hash = nh THEN SignedBlock(a, src, "open", 0, sk) ELSE received[n][hash]]]

CreateReceiveBlock(a, sk, ph, sender) ==
  /\ lastHash # NoHashVal
  /\ sender \notin ClaimedBy(ph)
  /\ LET nh == CalculateHash(BlockContent(a, ph, "receive", sender), ph) IN
     /\ lastHash' = nh
     /\ ledger' = [Node |-> [hash |-> IF hash = nh THEN SignedBlock(a, ph, "receive", sender, sk) ELSE ledger[Node][hash]]]
     /\ received' = [n \in Node |-> [hash |-> IF hash = nh THEN SignedBlock(a, ph, "receive", sender, sk) ELSE received[n][hash]]]

CreateChangeRepBlock(a, sk) ==
  /\ lastHash # NoHashVal
  /\ LET nh == CalculateHash(BlockContent(a, lastHash, "change_rep", 0), lastHash) IN
     /\ lastHash' = nh
     /\ ledger' = [Node |-> [hash |-> IF hash = nh THEN SignedBlock(a, lastHash, "change_rep", 0, sk) ELSE ledger[Node][hash]]]
     /\ received' = [n \in Node |-> [hash |-> IF hash = nh THEN SignedBlock(a, lastHash, "change_rep", 0, sk) ELSE received[n][hash]]]

\* Validation checks the signature, the presence of the referenced block, and
\* the type-specific rule (e.g. no overdraft for a send block).
ValidateAt(n, h) ==
  /\ received[n][h] # NoBlockVal
  /\ LET s == received[n][h] IN
     /\ s.sig = sk
     /\ ledger[n][s.blk.p] # NoBlockVal
     /\ \/ s.blk.t = "genesis"
        \/ (s.blk.t = "open")
        \/ (s.blk.t = "send" /\ Summarize(lastHash) >= s.blk.u)
        \/ (s.blk.t = "receive" /\ s.blk.u \notin ClaimedBy(s.blk.p))
  /\ ledger' = [ledger EXCEPT ![n][h] = s]
  /\ received' = [received EXCEPT ![n][h] = NoBlockVal]
  /\ UNCHANGED lastHash

Next ==
  \/ \E sk \in PrivateKey : CreateGenesisBlock(sk)
  \/ \E a \in PublicKey, sk \in PrivateKey, b \in Node, amt \in 1..GenesisBalance : CreateSendBlock(a, sk, b, amt)
  \/ \E a \in PublicKey, sk \in PrivateKey, src \in Hash : CreateOpenBlock(a, sk, src)
  \/ \E a \in PublicKey, sk \in PrivateKey, ph \in Hash, sender \in PublicKey : CreateReceiveBlock(a, sk, ph, sender)
  \/ \E a \in PublicKey, sk \in PrivateKey : CreateChangeRepBlock(a, sk)
  \/ \E n \in Node, h \in Hash : ValidateAt(n, h)

Spec == Init /\ [][Next]_vars

\* Type invariant: the three state variables stay within their declared types.
TypeInvariant ==
  /\ lastHash \in {NoHashVal} \cup Hash
  /\ ledger \in [Node -> [Hash -> SignedBlock \cup {NoBlockVal}]]
  /\ received \in [Node -> [Hash -> SignedBlock \cup {NoBlockVal}]]

\* Cryptographic invariant: every block in every node's copy of the ledger has
\* a signature that checks out against the owning account's public key.
SafetyInvariant ==
  \A n \in Node, h \in Hash :
    ledger[n][h] # NoBlockVal => ledger[n][h].sig = ledger[n][h].blk.a

====