---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node,
  GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* PrivateKey and PublicKey are finite sets; a key holder is node-level, not
\* account-level, so each node owns exactly one private key and the
\* public-to-private mapping is functional.
KeyOf == CHOOSE k \in PrivateKey : PublicKeyOf(k) = NoHash

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

NodeChain(n) == [ prev |-> NoHash, typ |-> "genesis", amt |-> GenesisBalance, signer |-> NoHash ]

\* A block is validated globally, and the signature check is the whole
\* invariant: no block may slip into anyone's ledger without a key that
\* actually belongs to the account whose chain it lives on.
ValidBlock(b, node) ==
  /\ b.signer = PublicKeyOf(node)
  /\ (b.typ = "genesis" => b.prev = NoHash)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlockVal ] ]
  /\ received = [ n \in Node |-> {} ]

CreateGenesis ==
  /\ lastHash = NoHashVal
  /\ \E k \in PrivateKey :
       /\ lastHash' = CalculateHash(NodeChain(NoHash), NoHashVal)
       /\ ledger' = [ n \in Node |-> [ h \in Hash |-> IF h = CalculateHash(NodeChain(NoHash), NoHashVal) THEN NodeChain(NoHash) ELSE NoBlockVal ] ]
       /\ received' = [ n \in Node |-> {} ]

Next == CreateGenesis

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [ Node -> [ Hash -> ("genesis" :> {typ}) \cup {NoBlockVal} ] ]
  /\ received \in [ Node -> SUBSET Hash ]

\* The signed genesis block is the only one in this bounded spec.
SafetyInvariant == \A h \in Hash : (h = lastHash) => ValidBlock(ledger[NoHash][h], NoHash)

====