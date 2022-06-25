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

\* @type: MESSAGE_TYPE;
RequestVoteRequest == "RequestVoteRequest_OF_MESSAGE_TYPE"
\* @type: MESSAGE_TYPE;
RequestVoteResponse == "RequestVoteResponse_OF_MESSAGE_TYPE"
\* @type: MESSAGE_TYPE;
AppendEntriesRequest == "AppendEntriesRequest_OF_MESSAGE_TYPE"
\* @type: MESSAGE_TYPE;
AppendEntriesResponse == "AppendEntriesResponse_OF_MESSAGE_TYPE"

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
    \* @type: SERVER -> Seq(LOG_ITEM);
    log

VARIABLES
    \* @type: SERVER -> Set(SERVER);
    votesResponded,

    \* @type: SERVER -> Set(SERVER);
    votesGranted,

    \* @type: SERVER -> SERVER -> Seq(LOG_ITEM);
    voterLog

INSTANCE Raft
====
