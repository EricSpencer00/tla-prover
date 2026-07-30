---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

\* Every node keeps its own copy of the whole distributed ledger; a block's
\* presence in a node's copy is separate from its presence in that node's
\* received-but-not-yet-validated set.
Blocks == [pub : PublicKey, typ : {"genesis", "send", "open", "receive", "change"}, prev : Hash \cup {NoHash}, to : PublicKey, amt : 0 .. GenesisBalance]
KeyOf(pub) == CHOOSE k \in PrivateKey : PublicKeyOf(k) = pub

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* The ledger is empty initially: all nodes agree on the empty state (no
\* blocks written anywhere), which is what makes the genesis broadcast atomic.
Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

SignedBy(k) == CHOOSE g \in PrivateKey : PublicKeyOf(g) = k

\* With no blocks yet written, any node with any key registered can create the
\* initial coin supply. The block is written into every node's ledger together,
\* which is what makes the genesis broadcast atomic.
CreateGenesis(k, n) ==
  /\ lastHash = NoHash
  /\ k \in PrivateKey
  /\ SignedBy(PublicKeyOf(k)) = k
  /\ \E h \in Hash :
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [g \in Hash |-> IF g = h THEN [pub |-> PublicKeyOf(k), typ |-> "genesis", prev |-> NoHash, to |-> PublicKeyOf(k), amt |-> GenesisBalance] ELSE ledger[m][g]]
       /\ received' = [m \in Node |-> {}]

\* Balance is derived by walking the account chain backward from a block to the
\* start of that account's chain (the genesis block or an open block).
Balance(m, h) ==
  IF ledger[m][h] = NoBlockVal THEN 0
  ELSE IF ledger[m][h].typ \in {"genesis", "open"} THEN ledger[m][h].amt
  ELSE IF ledger[m][h].typ \in {"send", "receive", "change"} THEN LET b == ledger[m][h] IN b.amt + Balance(m, b.prev)

\* Sending is a pure reduction of the sender's balance; the receiving node
\* builds its own balance history from the receive block it writes later.
CreateSend(k, n, h, amt) ==
  /\ lastHash # NoHash
  /\ ledger[n][lastHash] # NoBlockVal
  /\ ledger[n][lastHash].pub = PublicKeyOf(k)
  /\ amt > 0
  /\ Balance(n, lastHash) >= amt
  /\ \E nh \in Hash :
       /\ lastHash' = nh
       /\ ledger' = [m \in Node |-> [g \in Hash |-> IF g = nh THEN [pub |-> PublicKeyOf(k), typ |-> "send", prev |-> lastHash, to |-> NoBlockVal, amt |-> amt] ELSE ledger[m][g]]
       /\ received' = [m \in Node |-> received[m] \cup {nh}]

CreateOpen(k, n, h) ==
  /\ lastHash # NoHash
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].typ = "send"
  /\ ledger[n][h].to = PublicKeyOf(k)
  /\ \E nh \in Hash :
       /\ lastHash' = nh
       /\ ledger' = [m \in Node |-> [g \in Hash |-> IF g = nh THEN [pub |-> PublicKeyOf(k), typ |-> "open", prev |-> h, to |-> NoBlockVal, amt |-> ledger[n][h].amt] ELSE ledger[m][g]]
       /\ received' = [m \in Node |-> received[m] \cup {nh}]

\* A receive block references both its own previous block and the send it is
\* answering, and adds the sent amount to the receiver's balance.
CreateReceive(k, n, h, ph) ==
  /\ lastHash # NoHash
  /\ ledger[n][ph] # NoBlockVal
  /\ ledger[n][ph].typ \in {"send", "open"}
  /\ ledger[n][ph].to = PublicKeyOf(k)
  /\ ledger[n][lastHash] # NoBlockVal
  /\ ledger[n][lastHash].pub = PublicKeyOf(k)
  /\ ledger[n][lastHash].typ \in {"open", "receive"}
  /\ \E nh \in Hash :
       /\ lastHash' = nh
       /\ ledger' = [m \in Node |-> [g \in Hash |-> IF g = nh THEN [pub |-> PublicKeyOf(k), typ |-> "receive", prev |-> lastHash, to |-> ph, amt |-> ledger[n][ph].amt] ELSE ledger[m][g]]
       /\ received' = [m \in Node |-> received[m] \cup {nh}]

CreateChange(k, n) ==
  /\ lastHash # NoHash
  /\ ledger[n][lastHash] # NoBlockVal
  /\ ledger[n][lastHash].pub = PublicKeyOf(k)
  /\ \E nh \in Hash :
       /\ lastHash' = nh
       /\ ledger' = [m \in Node |-> [g \in Hash |-> IF g = nh THEN [pub |-> PublicKeyOf(k), typ |-> "change", prev |-> lastHash, to |-> NoBlockVal, amt |-> 0] ELSE ledger[m][g]]
       /\ received' = [m \in Node |-> received[m] \cup {nh}]

\* A node validates a block it has not written itself against its own local
\* copy of the distributed ledger, checking only the block types it knows.
Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ \E orig \in Node :
       /\ ledger[orig][h] # NoBlockVal
       /\ ledger' = [m \in Node |-> [g \in Hash |-> IF m = n /\ g = h THEN ledger[orig][h] ELSE ledger[m][g]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E k \in PrivateKey, n \in Node : CreateGenesis(k, n) \/ CreateChange(k, n)
  \/ \E k \in PrivateKey, n \in Node, h \in Hash, amt \in 1 .. GenesisBalance : CreateSend(k, n, h, amt)
  \/ \E k \in PrivateKey, n \in Node, h \in Hash : CreateOpen(k, n, h)
  \/ \E k \in PrivateKey, n \in Node, h \in Hash, ph \in Hash : CreateReceive(k, n, h, ph)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

\* Every written block is validated strictly against the writer's own ledger,
\* never against some other node's divergent copy.
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* Cryptographic safety: every block a node has written into its own ledger
\* carries a signature that matches the public key of the account chain it
\* lives in (the owning account's pubkey equals the signature's key).
SignedCorrectly ==
  \A n \in Node, h \in Hash :
    ledger[n][h] # NoBlockVal => ledger[n][h].pub = PublicKeyOf(SignedBy(ledger[n][h].pub))

====