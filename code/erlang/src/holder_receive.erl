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
%%% This module implements the behavior of a Holder (Receive) behavior
%%% mentioned in the "Holder Recieve Life Cycle" TLA+ specification.
%%% the transition rules can be found in the DOT specification.
%%%
%%% This module is expected to act as one of the participating entity
%%% for the Voucher Issue or Voucher Transfer behavior described in the
%%% TLA+ specification of the same name.
%%%
%%% This module is expected to interact with the VTP module.
%%%
%%% This module uses "hrlc" module to keep track of the states of the
%%% Holder (Receive)'s FSM.
%%% --------------------------------------------------------------------
-module(holder_receive).

-export([holder_receive/0]).

-import(logger,[log/1,log/2,log_final_state/2]). % @todo Use a proper logging framework
-import(hrlc, [init_fsm/1, init/2, prepare/2, abort/2, issue/2, transfer/2, cancel/2]).

%% ---------------------------------------------------------------------
%% Keeps track of various attributes of the holder.
%% ---------------------------------------------------------------------
-record(holder_data, {decision,state,action}).

%% ---------------------------------------------------------------------
%% Initialize the Holder (Receive)
%%
%% If an entity's state is not yet defined, you pass in "initialize" as
%% the state to initialize the entity to the starting state
%%
%% The spawned process can then be used to emulate a Holder (Receive)
%% entity whose behavior is defined in the Voucher Issue / Transfer
%% TLA+ specifications.
%% ---------------------------------------------------------------------
holder_receive() ->
    holder_receive([], #holder_data{decision=nil,state=initialize,action=nil}).

%% ---------------------------------------------------------------------
%% The various messages that is received by the Holder (Receive).
%%
%% propose_decision - This is the message sent to the Holder (Receive)
%% to initiate them before started to participate in a Voucher Issue /
%% Transfer transaction.
%%
%% query_decision - This is the message sent by the VTP process
%% (VtpPid) to check the current decision state of the Holder (Receive).
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
holder_receive(Holders, HolderData) ->
    receive
        {propose_decision, EntityPid, EntityType, Action, Decision} ->
	    case Action of
		transfer ->
		    log("[~p] ~p (receive) will take part in: ~p~n", [?MODULE, EntityType, Action]);
		issue ->
		    log("[~p] ~p (receive) will take part in: ~p~n", [?MODULE, EntityType, Action]);
		cancel ->
		    log("[~p] ~p (receive) will take part in: ~p~n", [?MODULE, EntityType, Action]);
		_ ->
		    log("[~p] !!! ~p (receive) cannot take part in ~p. !!!~n", [?MODULE, EntityType, Action]),
		    log("[~p] !!! Voucher transaction has terminated. !!!~n", [?MODULE]),
		    erlang:halt(1)
	    end,
            log("[~p] ~p will propose: ~p~n", [?MODULE, EntityType, Decision]),
	    FsmPid = hrlc:init_fsm(HolderData#holder_data.state),
	    State = hrlc:init(FsmPid, HolderData#holder_data.state),
	    log("[~p] ~p (receive) has entered the state: ~p~n", [?MODULE, EntityType, State]),
            holder_receive([EntityPid|Holders], HolderData#holder_data{decision=Decision, state=State, action=Action});
        {query_decision, VtpPid} ->
            log("[~p] Holder (Receive) queried by VTP ~p~n", [?MODULE, VtpPid]),
	    State = case HolderData#holder_data.decision of
			yes ->
			    FsmPid = hrlc:init_fsm(HolderData#holder_data.state),
			    hrlc:prepare(FsmPid, HolderData#holder_data.state);
			no ->
			    HolderData#holder_data.state
		    end,
	    UpdatedHolderData = HolderData#holder_data{state=State},
	    log("[~p] holder (receive) has entered the state: ~p~n", [?MODULE, UpdatedHolderData#holder_data.state]),
            VtpPid ! {receive_decision, UpdatedHolderData#holder_data.decision, holder},
            holder_receive(Holders, UpdatedHolderData);
        {commit, VtpPid} ->
	    FsmPid = hrlc:init_fsm(HolderData#holder_data.state),
	    State = case HolderData#holder_data.action of
			issue ->
			    hrlc:issue(FsmPid, HolderData#holder_data.state);
			transfer ->
			    hrlc:transfer(FsmPid, HolderData#holder_data.state);
			cancel ->
			    hrlc:cancel(FsmPid, HolderData#holder_data.state)
		    end,
	    UpdatedHolderData = HolderData#holder_data{state=State},
	    log("[~p] holder (receive) has entered the state: ~p~n", [?MODULE, UpdatedHolderData#holder_data.state]),
            log_final_state(commit,"Holder (Receive)"),
            VtpPid ! {acknowledgement};
        {abort, VtpPid} ->
	    FsmPid = hrlc:init_fsm(HolderData#holder_data.state),
	    State = hrlc:abort(FsmPid, HolderData#holder_data.state),
	    UpdatedHolderData = HolderData#holder_data{state=State},
	    log("[~p] holder (receive) has entered the state: ~p~n", [?MODULE, UpdatedHolderData#holder_data.state]),
            log_final_state(abort,"Holder (Receive)"),
            VtpPid ! {acknowledgement}
    end.
