---- MODULE W4Od3m0p0t0 ----
EXTENDS Integers, FiniteSets

CONSTANTS Banks, Ledger, Lock, LastBank
ASSUME Lock \in 1..Bank
ASSUME LastBank \in 1..Bank
ASSUME Ledger \in 1..Bank
ASSUME Banks \subseteq 1..Bank

VARIABLES snapshot, holding, posting, crashed

TypeOK ==
    /\ snapshot \in 0..Bank
    /\ holding \in 1..Bank
    /\ posting \in 1..Bank
    /\ crashed \subseteq 1..Bank
    /\ \A b \in Banks : b \notin crashed
    /\ Lock = holding
    /\ LastBank = posting
    /\ snapshot # holding
    /\ snapshot # posting
    /\ snapshot # crashed
    /\ \A b \in Banks : b \in crashed \Rightarrow b \notin {holding, posting}

Init ==
    /\ snapshot = 0
    /\ holding = 0
    /\ posting = 0
    /\ crashed = {}
    /\ Lock = 0
    /\ LastBank = 0

Next ==
    \/ crashed' = crashed
    \/ crashed' = crashed \cup {posting}
    \/ crashed' = crashed \ {holding}
    \/ crashed' = crashed
    /\ snapshot' = snapshot
    /\ holding' = holding
    /\ posting' = posting
    /\ LastBank' = LastBank
    /\ Lock' = Lock
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # crashed
    /\ \A b \in Banks : b \in crashed' \Rightarrow b \notin {holding', posting'}
    /\ \A b \in Banks : b \notin crashed' \Rightarrow b \in {holding', posting'}
    /\ \A b \in Banks : b \in crashed' \Rightarrow b \notin {Lock', LastBank'}
    /\ \A b \in Banks : b \notin crashed' \Rightarrow b = Lock'
    /\ \A b \in Banks : b = LastBank'
    /\ snapshot' = snapshot \o Lock \o snapshot
    /\ snapshot' # snapshot
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # Lock
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot' # crashed
    /\ snapshot' # holding
    /\ snapshot' # posting
    /\ snapshot' # LastBank
    /\ snapshot'