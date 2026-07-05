---- MODULE SmokeEWD998_SC ----
EXTENDS Naturals, TLC, IOUtils, CSV, Sequences, FiniteSets

CSVFile ==
    "SmokeEWD998_SC" \o ToString(JavaTime) \o ".csv"

ASSUME 
    CSVWrite("BugFlags#Violation", <<>>, CSVFile)

Cmd == LET absolutePathOfTLC == TLCGet("config").install
       IN <<"java", "-jar",
          absolutePathOfTLC, 
          "-noTE",
          "-simulate",
          "SmokeEWD998.tla">>

ASSUME
    \A i \in 1..30 : \A bf \in SUBSET (1..6) :
        Cardinality(bf) # 1
        /\ LET ret == IOEnvExec([BF |-> bf, Out |-> CSVFile, PN |-> RandomElement(3..4)], Cmd)
           IN LET _case == CASE ret.exitValue =  0 -> LET _ == PrintT(<<JavaTime, bf>>) IN TRUE
                         [] ret.exitValue = 10 -> LET _ == PrintT(<<bf, "Assumption violation">>) IN TRUE
                         [] ret.exitValue = 12 -> LET _ == PrintT(<<bf, "Invariant violation (Inv)">>) IN TRUE
                         [] ret.exitValue = 13 -> LET _ == PrintT(<<bf, "Property violation (TDSpec)">>) IN TRUE
                         [] OTHER -> LET _ == PrintT(ret) IN TRUE
                   IN LET _csv == CSVWrite("%1$s#%2$s", <<bf, ret.exitValue>>, CSVFile) IN TRUE

====