------------------------------- MODULE Universal -------------------------------
(***************************************************************************)
(* Formal Specification in TLA^+ of the                                    *)
(* Interledger Protocol Universal (ILP/U)                                  *)
(*                                                                         *)
(*`.                                                                       *)
(* Modeled after the excellent Raft specification by Diego Ongaro.         *)
(*   Available at https://github.com/ongardie/raft.tla                     *)
(*                                                                         *)
(*   Copyright 2014 Diego Ongaro.                                          *)
(*   This work is licensed under the Creative Commons Attribution-4.0      *)
(*   International License https://creativecommons.org/licenses/by/4.0/  .'*)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Bags, TLC

\* The set of ledger IDs
CONSTANTS Ledger

\* The set of participant IDs
CONSTANTS Participant

\* Sender states
CONSTANTS S_Ready, S_Waiting, S_Done

\* Ledger states
CONSTANTS L_Proposed, L_Prepared, L_Executed, L_Aborted

\* Message types
CONSTANTS PrepareRequest, ExecuteRequest, AbortRequest,
          PrepareNotify, ExecuteNotify, AbortNotify

\* Receipt signature
CONSTANTS R_ReceiptSignature

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another.
VARIABLE messages

\* Under synchrony we are allowed to have a global clock
VARIABLE clock

----
\* Sender variables

\* State of the sender (S_Ready, S_Waiting, S_Done)
VARIABLE senderState

\* All sender variables
senderVars == <<senderState>>
----
\* The following variables are all per ledger (functions with domain Ledger)

\* The ledger state (L_Proposed, L_Prepared, L_Executed or L_Aborted)
VARIABLE ledgerState

\* The timeouts for each of the the transfers
VARIABLE ledgerExpiration

\* All ledger variables
ledgerVars == <<ledgerState, ledgerExpiration>>
----

\* All variables; used for stuttering (asserting state hasn't changed)
vars == <<clock, messages, senderVars, ledgerVars>>

----
\* Helpers

\* Add a set of new messages in transit 
Broadcast(m) == messages' = messages (+) SetToBag(m)

\* Add a message to the bag of messages
Send(m) == Broadcast({m})

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = messages (-) SetToBag({m})

\* Respond to a message by sending multiple messages
ReplyBroadcast(responses, request) ==
    messages' = messages (-) SetToBag({request}) (+) SetToBag(responses)

\* Combination of Send and Discard
Reply(response, request) ==
    ReplyBroadcast({response}, request)


\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Is a final ledger state
IsFinalLedgerState(i) == i \in {L_Executed, L_Aborted}

----
\* Define type specification for all variables

TypeOK == /\ clock \in Nat
          /\ IsABag(messages)
          /\ senderState \in {S_Ready, S_Waiting, S_Done}
          /\ ledgerState \in [Ledger -> {L_Proposed, L_Prepared, L_Executed, L_Aborted}]

----
\* Define initial values for all variables

InitSenderVars == /\ senderState = S_Ready

InitLedgerVars == /\ ledgerState = [i \in Ledger |-> L_Proposed]
                  /\ ledgerExpiration = [i \in Ledger |-> 4 * Cardinality(Ledger) + 2 - i]

Init == /\ clock = 0
        /\ messages = EmptyBag
        /\ InitSenderVars
        /\ InitLedgerVars

----
\* Define state transitions

\* Participant i starts off the chain
Start(i) ==
    /\ senderState = S_Ready
    /\ senderState' = S_Waiting
    /\ Send([mtype   |-> PrepareRequest,
             msource |-> i,
             mdest   |-> i+1])
    /\ UNCHANGED <<ledgerVars>>

\* Ledger spontaneously aborts
LedgerAbort(l) ==
    /\ ledgerState[l] = L_Proposed
    /\ ledgerState' = [ledgerState EXCEPT ![l] = L_Aborted]
    /\ Send([mtype   |-> AbortNotify,
             msource |-> l,
             mdest   |-> l-1])
    /\ UNCHANGED <<senderVars, ledgerExpiration>>

LedgerTimeout(l) ==
    /\ \lnot IsFinalLedgerState(ledgerState[l])
    /\ ledgerExpiration[l] =< clock
    /\ ledgerState' = [ledgerState EXCEPT ![l] = L_Aborted]
    /\ Send([mtype   |-> AbortNotify,
             msource |-> l,
             mdest   |-> l-1])
    /\ UNCHANGED <<senderVars, ledgerExpiration>>

NothingHappens ==
    /\ clock \leq Max({ledgerExpiration[x] : x \in Ledger})
    /\ BagCardinality(messages) = 0
    /\ senderState # S_Ready
    /\ UNCHANGED <<messages, senderVars, ledgerVars>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a Prepare request from participant j
HandlePrepareRequest(i, j, m) ==
    LET valid == /\ ledgerState[i] = L_Proposed
                 /\ j = i - 1
    IN \/ /\ valid
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Prepared]
          /\ Reply([mtype   |-> PrepareNotify,
                    msource |-> i,
                    mdest   |-> i+1], m)
          /\ UNCHANGED <<senderVars, ledgerExpiration>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars>>

\* Server i receives an Execute request from server j
HandleExecuteRequest(i, j, m) ==
    LET valid == /\ ledgerState[i] = L_Prepared
                 /\ m.mreceipt = R_ReceiptSignature
    IN \/ /\ valid
          /\ ledgerState' = [ledgerState EXCEPT ![i] = L_Executed]
          /\ Reply([mtype    |-> ExecuteNotify,
                    msource  |-> i,
                    mdest    |-> i-1,
                    mreceipt |-> m.mreceipt], m)
          /\ UNCHANGED <<senderVars, ledgerExpiration>>
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars>>

\* Ledger j notifies participant i that the transfer is prepared
HandlePrepareNotify(i, j, m) ==
    LET isRecipient == i = Max(Participant)
    IN \/ /\ isRecipient
          /\ Reply([mtype    |-> ExecuteRequest,
                    msource  |-> i,
                    mdest    |-> i-1,
                    mreceipt |-> R_ReceiptSignature], m)
          /\ UNCHANGED <<senderVars, ledgerVars>>
       \/ /\ \lnot isRecipient
          /\ Reply([mtype   |-> PrepareRequest,
                    msource |-> i,
                    mdest   |-> i+1], m)
          /\ UNCHANGED <<senderVars, ledgerVars>>

\* Ledger j notifies participant i that the transfer is executed
HandleExecuteNotify(i, j, m) ==
    LET isSender == i = Min(Participant)
    IN \/ /\ \lnot isSender
          /\ Reply([mtype    |-> ExecuteRequest,
                    msource  |-> i,
                    mdest    |-> i-1,
                    mreceipt |-> m.mreceipt], m)
          /\ UNCHANGED <<senderVars, ledgerVars>>
       \/ /\ isSender
          /\ senderState = S_Waiting
          /\ senderState' = S_Done
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars>>
       \/ /\ isSender
          /\ senderState # S_Waiting
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars>>

\* Ledger j notifies participant i that the transfer is aborted
HandleAbortNotify(i, j, m) ==
    LET isSenderAndWaiting == /\ i = Min(Participant)
                              /\ \/ senderState = S_Waiting
                                 \/ senderState = S_Ready
    IN \/ /\ isSenderAndWaiting
          /\ senderState' = S_Done
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars>>
       \/ /\ \lnot isSenderAndWaiting
          /\ Discard(m)
          /\ UNCHANGED <<senderVars, ledgerVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \/ /\ m.mtype = PrepareRequest
          /\ HandlePrepareRequest(i, j, m)
       \/ /\ m.mtype = ExecuteRequest
          /\ HandleExecuteRequest(i, j, m)
       \/ /\ m.mtype = PrepareNotify
          /\ HandlePrepareNotify(i, j, m)
       \/ /\ m.mtype = ExecuteNotify
          /\ HandleExecuteNotify(i, j, m)
       \/ /\ m.mtype = AbortNotify
          /\ HandleAbortNotify(i, j, m)

\* End of message handlers.
----
\* Defines how the variables may transition.

Termination == 
    /\ \A l \in Ledger : IsFinalLedgerState(ledgerState[l])
    /\ senderState = S_Done
    /\ UNCHANGED vars

Consistency ==
    \A l1, l2 \in Ledger : \lnot /\ ledgerState[l1] = L_Aborted
                                 /\ ledgerState[l2] = L_Executed

Next == \/ /\ \/ Start(Min(Participant))
              \/ \E l \in Ledger : LedgerAbort(l)
              \/ \E l \in Ledger : LedgerTimeout(l)
              \/ \E m \in DOMAIN messages : Receive(m)
              \/ NothingHappens   
           /\ clock' = clock + 1
        \/ Termination

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* The spec should be type-safe
THEOREM Spec => []TypeOK

=============================================================================
