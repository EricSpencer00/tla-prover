---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* lastHash: the previous block's hash, used as input to the next one.
\* ledger: each node's copy of the distributed ledger (hash -> SignedBlock/NoBlockVal).
\* recv: blocks each node has received but not yet validated.
VARIABLES lastHash, ledger, recv

SignedBlock == [hash: Hash, owner: PublicKey, prev: Hash, amt: 0..GenesisBalance, typ: {"genesis", "send", "open", "receive", "change", "noop"}, sig: PrivateKey]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> SignedBlock \cup {NoBlockVal}]]
  /\ recv \in [Node -> SUBSET SignedBlock]

UNION == ledger[Node1] \cup ledger[Node2] \cup ledger[Node3]

RECURSIVE SumChainOver(_)
SumChainOver(S) ==
  IF S = {} THEN 0
  ELSE LET bb == CHOOSE b \in S : TRUE IN bb.amt + SumChainOver(S \ {bb})

SumBalances ==
  LET S == {ledger[n][h] : n \in {Node1, Node2, Node3}, h \in Hash, ledger[n][h] # NoBlockVal} \cup {NoBlockVal}
  IN SumChainOver(S)

\* A valid signature is a private key that maps to the block's owner public key.
ValidSignature(k) == k \in PrivateKey /\ PubKeyOf(k) = (CHOOSE b \in ledger[Node1] \cup ledger[Node2] \cup ledger[Node3] : b # NoBlockVal /\ b.sig = k)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in {Node1, Node2, Node3} |-> [h \in Hash |-> NoBlockVal]]
  /\ recv = [n \in {Node1, Node2, Node3} |-> {}]

\* Genesis block creation is a one-shot event that also seeds all node ledgers.
CreateGenesis(k) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash([hash |-> NoHashVal, owner |-> PubKeyOf(k), typ |-> "genesis"], NoHash)
  /\ ledger' = [n \in {Node1, Node2, Node3} |-> [ledger[n] EXCEPT ![lastHash'] = [hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> NoHashVal, amt |-> GenesisBalance, typ |-> "genesis", sig |-> k]]]
  /\ recv' = [n \in {Node1, Node2, Node3} |-> recv[n] \cup {[hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> NoHashVal, amt |-> GenesisBalance, typ |-> "genesis", sig |-> k]}]

\* Send block: deduct from sender and reference its own previous block.
CreateSend(n, k, amt) ==
  /\ lastHash # NoHashVal
  /\ ledger[n][lastHash] # NoBlockVal
  /\ amt <= ledger[n][lastHash].amt
  /\ lastHash' = CalculateHash([hash |-> lastHash, owner |-> PubKeyOf(k), amt |-> amt, typ |-> "send"], NoHash)
  /\ ledger' = [m \in {Node1, Node2, Node3} |-> [ledger[m] EXCEPT ![lastHash'] = [hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> lastHash, amt |-> amt, typ |-> "send", sig |-> k]]]
  /\ recv' = [m \in {Node1, Node2, Node3} |-> recv[m] \cup {[hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> lastHash, amt |-> amt, typ |-> "send", sig |-> k]}]

\* Open block: establish a new account's first block, referencing a send.
CreateOpen(n, k, s) ==
  /\ s.typ = "send" /\ s.owner # PubKeyOf(k)
  /\ ledger[n][s.prev] # NoBlockVal /\ ledger[n][s.prev].typ # "open"
  /\ lastHash' = CalculateHash([hash |-> lastHash, owner |-> PubKeyOf(k), amt |-> s.amt, typ |-> "open"], NoHash)
  /\ ledger' = [m \in {Node1, Node2, Node3} |-> [ledger[m] EXCEPT ![lastHash'] = [hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> s.prev, amt |-> s.amt, typ |-> "open", sig |-> k]]]
  /\ recv' = [m \in {Node1, Node2, Node3} |-> recv[m] \cup {[hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> s.prev, amt |-> s.amt, typ |-> "open", sig |-> k]}]

\* Receive block: credit a sent amount, referencing both prior and send blocks.
CreateReceive(n, k, s) ==
  /\ s.typ = "send" /\ s.owner # PubKeyOf(k)
  /\ ledger[n][s.prev] # NoBlockVal /\ ledger[n][s.prev].typ # "receive"
  /\ lastHash' = CalculateHash([hash |-> lastHash, owner |-> PubKeyOf(k), amt |-> s.amt, typ |-> "receive"], NoHash)
  /\ ledger' = [m \in {Node1, Node2, Node3} |-> [ledger[m] EXCEPT ![lastHash'] = [hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> s.prev, amt |-> s.amt, typ |-> "receive", sig |-> k]]]
  /\ recv' = [m \in {Node1, Node2, Node3} |-> recv[m] \cup {[hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> s.prev, amt |-> s.amt, typ |-> "receive", sig |-> k]}]

\* Change representative block: rotate the voting delegate.
CreateChange(n, k) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash([hash |-> lastHash, owner |-> PubKeyOf(k), typ |-> "change"], NoHash)
  /\ ledger' = [m \in {Node1, Node2, Node3} |-> [ledger[m] EXCEPT ![lastHash'] = [hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> lastHash, amt |-> 0, typ |-> "change", sig |-> k]]]
  /\ recv' = [m \in {Node1, Node2, Node3} |-> recv[m] \cup {[hash |-> lastHash', owner |-> PubKeyOf(k), prev |-> lastHash, amt |-> 0, typ |-> "change", sig |-> k]}]

\* Process: a node validates a received block against its own ledger copy.
Process(n, x) ==
  /\ x \in recv[n]
  /\ x.sig \in PrivateKey /\ PubKeyOf(x.sig) = x.owner
  /\ (x.prev \in {NoHashVal} \cup {y \in Hash : ledger[n][y] # NoBlockVal}) /\ (x.typ \in {"genesis", "change"} \/ x.prev \in Hash)
  /\ (x.typ = "send" => ledger[n][x.prev].amt >= x.amt)
  /\ (x.typ = "receive" => ledger[n][x.prev].typ # "receive")
  /\ ledger' = [ledger EXCEPT ![n][x.hash] = x]
  /\ recv' = [recv EXCEPT ![n] = @ \ {x}]
  /\ UNCHANGED lastHash

\* The no-op action keeps the model from stalling when no block is creatable.
Idle == UNCHANGED <<lastHash, ledger, recv>>

Next ==
  \/ Idle
  \/ (\E k \in PrivateKey : CreateGenesis(k))
  \/ (\E n \in {Node1, Node2, Node3}, k \in PrivateKey, amt \in 1..GenesisBalance : CreateSend(n, k, amt))
  \/ (\E n \in {Node1, Node2, Node3}, k \in PrivateKey, s \in UNION : CreateOpen(n, k, s))
  \/ (\E n \in {Node1, Node2, Node3}, k \in PrivateKey, s \in UNION : CreateReceive(n, k, s))
  \/ (\E n \in {Node1, Node2, Node3}, k \in PrivateKey : CreateChange(n, k))
  \/ (\E n \in {Node1, Node2, Node3}, x \in recv[n] : Process(n, x))

Spec == Init /\ [][Next]_<<lastHash, ledger, recv>>

\* The type invariant covers lastHash, ledger, and recv; the crypto invariant
\* covers the signature/public-key relationship for every recorded block.
SafetyInvariant == TypeOK /\ (\A n \in {Node1, Node2, Node3}, h \in Hash : ledger[n][h] # NoBlockVal => ValidSignature(ledger[n][h].sig))
====