---- MODULE MC ----

\* @type: Set(SERVER);
Server == {
    "sv1_OF_SERVER",
    "sv2_OF_SERVER",
    "sv3_OF_SERVER",
    "sv4_OF_SERVER",
    "sv5_OF_SERVER"
    }

\* @type: STATE;
Follower == "Follower_OF_STATE"
\* @type: STATE;
Candidate == "Candidate_OF_STATE"
\* @type: STATE;
Leader == "Leader_OF_STATE"

VARIABLE
    \* @type: MESSAGE -> Int;
    messages

VARIABLES
    \* @type: SERVER -> Int;
    currentTerm,

    \* @type: SERVER -> STATE;
    state,

    \* @type: SERVER -> Seq(SERVER);
    votedFor

VARIABLES
    \* @type: SERVER -> Set(SERVER);
    votesResponded,

    \* @type: SERVER -> Set(SERVER);
    votesGranted,

    \* @type: SERVER -> SERVER -> Seq(LOG_ITEM);
    voterLog

INSTANCE Raft
====
