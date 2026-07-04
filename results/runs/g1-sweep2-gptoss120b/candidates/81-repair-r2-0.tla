---- MODULE EWD998_optsSC ----
EXTENDS TLC, IOUtils, Naturals, Sequences, CSV

Features ==
    {"pt1","pt2","pt3","pt4","pt5"}

Nodes ==
    {7,29,43}
    \* {7, 19, 29, 37, 43}

\* Filename for the CSV file that appears also in the R script and is passed
\* to the nested TLC instances that are forked below.
CSVFile ==
    "EWD998_opts_" \o ToString(JavaTime) \o ".csv"

\* Write column headers to CSV file at startup of TLC instance that "runs"
\* this script and forks the nested instances of TLC that simulate the spec
\* and collect the statistics.
ASSUME 
    CSVWrite("Variant#Node#Length#T#T2TD#InitiateProbe#PassToken#SendMsg#RecvMsg#Deactivate",
             <<>>, CSVFile)

\* Command to fork nested TLC instances that simulate the spec and collect the
\* statistics. TLCGet("config").install gives the path to the TLC jar also
\* running this script.
Cmd == LET absolutePathOfTLC == TLCGet("config").install
       IN <<"java", "-jar",
          absolutePathOfTLC, 
          "-deadlock", "-noTE",
          "-depth", "-1",
          "-workers", "auto",
          "-generate", "num=10",
          "-config", "EWD998_opts.tla",
          "EWD998_opts.tla">>

\* Run the nested TLC instances for every combination of features and nodes.
\* The ASSUME must evaluate to a Boolean; we use IF…THEN…ELSE to guarantee
\* a Boolean result while preserving the original side‑effects (printing).
ASSUME 
    \A features \in SUBSET Features:
        \A n \in Nodes:
            LET ret == IOEnvExec([N |-> n, F |-> features, Out |-> CSVFile], Cmd).exitValue
            IN 
                IF ret = 0 THEN
                    LET _ == PrintT(<<JavaTime, n, features>>)
                    IN TRUE
                ELSE IF ret = 10 THEN
                    LET _ == PrintT(<<n, features, "Assumption violation">>)
                    IN TRUE
                ELSE IF ret = 12 THEN
                    LET _ == PrintT(<<n, features, "Safety violation">>)
                    IN TRUE
                ELSE IF ret = 13 THEN
                    LET _ == PrintT(<<n, features, "Liveness violation">>)
                    IN TRUE
                ELSE
                    LET _ == Print(<<n, features,
                                    IOEnvExec([N |-> n, F |-> features, Out |-> CSVFile], Cmd),
                                    "Error">>, FALSE)
                    IN FALSE
=============================================================================