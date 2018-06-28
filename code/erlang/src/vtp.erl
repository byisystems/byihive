%%% --------------------------------------------------------------------
%%% @copyright 2018, Backyard Innovations Pte. Ltd., Singapore.
%%%
%%% Released under the terms of the GNU Affero General Public License
%%% v3.0. See: file LICENSE that came with this software for details.
%%%
%%% This file contains Intellectual Property that belongs to
%%% Backyard Innovations Pte Ltd., Singapore.
%%%
%%% @author Santhosh Raju <santhosh@byisystems.com>
%%% @author Cherry G. Mathew <cherry@byisystems.com>
%%% --------------------------------------------------------------------

%%% --------------------------------------------------------------------
%%% This module implements the behavior of a Voucher Transaction
%%% Provider (VTP) as mentioned in the "Voucher Issue / Redeem /
%%% Transfer / Cancel" TLA+ specifications.
%%%
%%% This module implements the Two-Phase Commit protocol as described
%%% in the TLA+ specifications mentioned above.
%%%
%%% The module takes exactly two entities (Issuer / Holder / Collector)
%%% and either commits or aborts the transaction based.
%%%
%%% @todo The module is currently not aware of the "Vouchers" and hence
%%% the implementation is not yet complete
%%% --------------------------------------------------------------------
-module(vtp).

-export([vtp/0]).

-import(logger,[log/1,log/2,log_final_state/2]). % @todo Use a proper logging framework

%% ---------------------------------------------------------------------
%% Keeps track of various attributes of the VTP
%% ---------------------------------------------------------------------
-record(vtp_messages, {messages}).

%% ---------------------------------------------------------------------
%% Initialize the VTP
%%
%% The spawned process can then be used to emulate a VTP to which
%% entities (Issuer / Holder / Collector) can be added after which one
%% can begin to initiate a Two-Phase Commit.
%% ---------------------------------------------------------------------
vtp() ->
    vtp([], [], [], #vtp_messages{messages=[]}).

%% ---------------------------------------------------------------------
%% The various messages that is received by the VTP.
%%
%% add_entity - This message helps add an entity which will participate
%% in a Two-Phase Commit. The EntityPid is added so that the VTP can
%% can pass messages to the parties involved in a transaction and
%% coordinate in making a decision.
%%
%% add_voucher - This message helps add a voucher which will be
%% transmitted between the entities. The VoucherPid is added so that
%% the VTP can query or set various voucher properties.
%%
%% vtp_start - Initiates the phase 1 of the Two-Phase Commit protocol
%%
%% receive_decision - These are the decisions send by entities for the
%% current transaction. The VTP then checks to see if all the entities
%% involved are "prepared" to commit or not. In the current
%% implementation we pass around the atoms "yes" or "no" to indicate an
%% Entity's preparedness.
%% ---------------------------------------------------------------------
vtp(Entities, Vouchers, Clients, #vtp_messages{messages = Messages} = VtpMessages) ->
    receive
        {add_entity, EntityPid, EntityType} ->
            log("[~p] Added ~p: ~p~n", [?MODULE, EntityType, EntityPid]),
            vtp([EntityPid|Entities], Vouchers, Clients, VtpMessages);
	{add_voucher, VoucherPid} ->
	    log("[~p] Added voucher: ~p~n", [?MODULE, VoucherPid]),
            vtp(Entities, [VoucherPid|Vouchers], Clients, VtpMessages);
        {vtp_start, ClientPid} ->
            log("[~p] 1st phase, gather the votes ~n", [?MODULE]),
	    % This is basically the VTP querying each of entities
	    % to see if they are "prepared" for the transaction.
            vtp_broadcast(Entities, {query_decision, self()}),
	    vtp(Entities, Vouchers, [ClientPid|Clients], VtpMessages);
        {receive_decision, Decision, EntityType} ->
            log("[~p] received a ~p from ~p~n", [?MODULE, Decision, EntityType]),
            NewMessages = [Decision|Messages],
            VotingFinished = length(NewMessages) == length(Entities),
            case VotingFinished of
                true ->
                    vtp_decide(Entities, Vouchers, Clients, NewMessages);
                false ->
                    UpdatedVtpMessages = VtpMessages#vtp_messages{messages=NewMessages},
                    vtp(Entities, Vouchers, Clients, UpdatedVtpMessages)
            end
    end.

%% ---------------------------------------------------------------------
%% This function starts the second phase of the Two-Phase Commit
%% protocol. The end result would be to "commit" the transaction if all
%% the Entities "agree" or "abort" if any of the Entity "disagree"
%% ---------------------------------------------------------------------
vtp_decide(Entities, Vouchers, Clients, Messages) ->
    log("[~p] 2nd phase, try to commit ~n", [?MODULE]),
    Consensus = lists:all(fun(Message) -> Message == yes end, Messages),
    Decision = case Consensus of
        true ->
            commit;
        false ->
            abort
    end,
    vtp_broadcast(Vouchers, {Decision, self()}),
    vtp_broadcast(Entities, {Decision, self()}),
    vtp_wait_acknowledgements(length(Entities), Clients, Decision).

%% ---------------------------------------------------------------------
%% This group of functions, receive the acknowlegement of the decision
%% taken by VTP from all the Entities involved in the Two-Phase Commit
%% protocol.
%% ---------------------------------------------------------------------
vtp_wait_acknowledgements(0, Clients, Decision) ->
    log_final_state(Decision, "VTP"),
    vtp_broadcast(Clients, {vtp_end});
vtp_wait_acknowledgements(RemainingEntitiesNumber, Clients, Decision) ->
    receive
        {acknowledgement} ->
	    vtp_wait_acknowledgements(RemainingEntitiesNumber - 1, Clients, Decision)
    end.

%% ---------------------------------------------------------------------
%% This function broadcasts the Message to all the Recipients involved
%% in the Two-Phase Commit.
%%
%% Recipients is a list of Pids of Recipients who are involved in the
%% Two-Phase Commit.
%% ---------------------------------------------------------------------
vtp_broadcast(Recipients, Message) ->
    [RecipientPid ! Message || RecipientPid <- Recipients].
