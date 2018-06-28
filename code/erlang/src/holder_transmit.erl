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
%%% This module implements the behavior of a Holder (Transmit) behavior
%%% mentioned in the "Holder Recieve Life Cycle" TLA+ specification.
%%% the transition rules can be found in the DOT specification.
%%%
%%% This module is expected to act as one of the participating entity
%%% for the Voucher Issue or Voucher Transfer behavior described in the
%%% TLA+ specification of the same name.
%%%
%%% This module is expected to interact with the VTP module.
%%%
%%% This module uses "htlc" module to keep track of the states of the
%%% Holder (Transmit)'s FSM.
%%% --------------------------------------------------------------------
-module(holder_transmit).

-export([holder_transmit/0]).

-import(logger,[log/1,log/2,log_final_state/2]). % @todo Use a proper logging framework
-import(htlc, [init_fsm/1, init/2, prepare/2, abort/2, redeem/2, transfer/2]).

%% ---------------------------------------------------------------------
%% Keeps track of various attributes of the holder.
%% ---------------------------------------------------------------------
-record(holder_data, {decision,state,action}).

%% ---------------------------------------------------------------------
%% Initialize the Holder (Transmit)
%%
%% If an entity's state is not yet defined, you pass in "initialize" as
%% the state to initialize the entity to the starting state
%%
%% The spawned process can then be used to emulate a Holder (Transmit)
%% entity whose behavior is defined in the Voucher Issue / Transfer
%% TLA+ specifications.
%% ---------------------------------------------------------------------
holder_transmit() ->
    holder_transmit([], #holder_data{decision=nil,state=initialize,action=nil}).

%% ---------------------------------------------------------------------
%% The various messages that is transmitted by the Holder (Transmit).
%%
%% propose_decision - This is the message sent to the Holder (Transmit)
%% to initiate them before started to participate in a Voucher Issue /
%% Transfer transaction.
%%
%% query_decision - This is the message sent by the VTP process
%% (VtpPid) to check the current decision state of the Holder (Transmit).
%%
%% commit - This is the message sent by the VTP process (VtpPid) which
%% commits the current transaction when both parties in the Voucher
%% Issue / Transfer transaction is in agreement. An acknowledgement
%% is sent back by the Holder (Recieve).
%%
%% abort - This is the message sent by the VTP process (VtpPid) which
%% aborts the current transaction either or both the parties in the
%% Voucher Issue / Transfer transaction are not in agreement. An
%% acknowledgement is sent back by the Holder (Recieve).
%% ---------------------------------------------------------------------
holder_transmit(Holders, HolderData) ->
    receive
        {propose_decision, EntityPid, EntityType, Action, Decision} ->
	    case Action of
		transfer ->
		    log("[~p] ~p (transmit) will take part in: ~p~n", [?MODULE, EntityType, Action]);
		redeem ->
		    log("[~p] ~p (transmit) will take part in: ~p~n", [?MODULE, EntityType, Action]);
		_ ->
		    log("[~p] !!! ~p (transmit) cannot take part in ~p. !!!~n", [?MODULE, EntityType, Action]),
		    log("[~p] !!! Voucher transaction has terminated. !!!~n", [?MODULE]),
		    erlang:halt(1)
	    end,
            log("[~p] ~p (transmit) will propose: ~p~n", [?MODULE, EntityType, Decision]),
	    FsmPid = htlc:init_fsm(HolderData#holder_data.state),
	    State = htlc:init(FsmPid, HolderData#holder_data.state),
	    log("[~p] ~p (transmit) has entered the state: ~p~n", [?MODULE, EntityType, State]),
            holder_transmit([EntityPid|Holders], HolderData#holder_data{decision=Decision, state=State, action=Action});
        {query_decision, VtpPid} ->
            log("[~p] Holder (Transmit) queried by VTP ~p~n", [?MODULE, VtpPid]),
	    State = case HolderData#holder_data.decision of
			yes ->
			    FsmPid = htlc:init_fsm(HolderData#holder_data.state),
			    htlc:prepare(FsmPid, HolderData#holder_data.state);
			no ->
			    HolderData#holder_data.state
		    end,
	    UpdatedHolderData = HolderData#holder_data{state=State},
	    log("[~p] holder (transmit) has entered the state: ~p~n", [?MODULE, UpdatedHolderData#holder_data.state]),
            VtpPid ! {receive_decision, UpdatedHolderData#holder_data.decision, holder},
            holder_transmit(Holders, UpdatedHolderData);
        {commit, VtpPid} ->
	    FsmPid = htlc:init_fsm(HolderData#holder_data.state),
	    State = case HolderData#holder_data.action of
			redeem ->
			    htlc:redeem(FsmPid, HolderData#holder_data.state);
			transfer ->
			    htlc:transfer(FsmPid, HolderData#holder_data.state)
		    end,
	    UpdatedHolderData = HolderData#holder_data{state=State},
	    log("[~p] holder (transmit) has entered the state: ~p~n", [?MODULE, UpdatedHolderData#holder_data.state]),
            log_final_state(commit,"Holder (Transmit)"),
            VtpPid ! {acknowledgement};
        {abort, VtpPid} ->
	    FsmPid = htlc:init_fsm(HolderData#holder_data.state),
	    State = htlc:abort(FsmPid, HolderData#holder_data.state),
	    UpdatedHolderData = HolderData#holder_data{state=State},
	    log("[~p] holder (transmit) has entered the state: ~p~n", [?MODULE, UpdatedHolderData#holder_data.state]),
            log_final_state(abort,"Holder (Transmit)"),
            VtpPid ! {acknowledgement}
    end.
