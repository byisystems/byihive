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
%%% This module implements the behavior of a Collector behavior mentioned
%%% in the "Collector Life Cycle" TLA+ specification.The transition rules
%%% rules can be found in the DOT specification.
%%%
%%% This module is expected to act as one of the participating entity
%%% for the Voucher Issue or Voucher Cancel behavior described in the
%%% TLA+ specification of the same name.
%%%
%%% This module is expected to interact with the VTP module.
%%%
%%% This module uses "clc" module to keep track of the states of the
%%% Collector's FSM.
%%% --------------------------------------------------------------------
-module(collector).

-export([collector/0]).

-import(logger,[log/1,log/2,log_final_state/2]). % @todo Use a proper logging framework
-import(clc, [init_fsm/1, init/2, prepare/2, abort/2, issue/2, cancel/2]).

%% ---------------------------------------------------------------------
%% Keeps track of various attributes of the collector.
%% ---------------------------------------------------------------------
-record(collector_data, {decision,state,action}).

%% ---------------------------------------------------------------------
%% Initialize the Collector.
%%
%% If an entity's state is not yet defined, you pass in "initialize" as
%% the state to initialize the entity to the starting state
%%
%% The spawned process can then be used to emulate an Collector
%% entity whose behavior is defined in the Voucher Redeem
%% TLA+ specifications.
%% ---------------------------------------------------------------------
collector() ->
    collector([], #collector_data{decision=nil,state=initialize,action=nil}).

%% ---------------------------------------------------------------------
%% The various messages that is received by the Collector.
%%
%% propose_decision - This is the message sent to the Collector to
%% initiate them before started to participate in a Voucher Redeem
%% transaction.
%%
%% query_decision - This is the message sent by the VTP process
%% (VtpPid) to check the current decision state of the Collector.
%%
%% commit - This is the message sent by the VTP process (VtpPid) which
%% commits the current transaction when both parties in the Voucher
%% Redeem transaction is in agreement. An acknowledgement is
%% sent back by the Collector.
%%
%% abort - This is the message sent by the VTP process (VtpPid) which
%% aborts the current transaction either or both the parties in the
%% Voucher Redeem transaction are not in agreement. An
%% acknowledgement is sent back by the Collector.
%% ---------------------------------------------------------------------
collector(Collectors, CollectorData) ->
    receive
        {propose_decision, EntityPid, EntityType, Action, Decision} ->
	    case Action of
		redeem ->
		    log("[~p] ~p will take part in: ~p~n", [?MODULE, EntityType, Action]);
		_ ->
		    log("[~p] !!! ~p cannot take part in ~p. !!!~n", [?MODULE, EntityType, Action]),
		    log("[~p] !!! Voucher transaction has terminated. !!!~n", [?MODULE]),
		    erlang:halt(1)
	    end,
            log("[~p] ~p will propose: ~p~n", [?MODULE, EntityType, Decision]),
	    FsmPid = clc:init_fsm(CollectorData#collector_data.state),
	    State = clc:init(FsmPid, CollectorData#collector_data.state),
	    log("[~p] ~p has entered the state: ~p~n", [?MODULE, EntityType, State]),
            collector([EntityPid|Collectors], CollectorData#collector_data{decision=Decision, state=State, action=Action});
        {query_decision, VtpPid} ->
            log("[~p] Collector queried by VTP ~p~n", [?MODULE, VtpPid]),
	    State = case CollectorData#collector_data.decision of
			yes ->
			    FsmPid = clc:init_fsm(CollectorData#collector_data.state),
			    clc:prepare(FsmPid, CollectorData#collector_data.state);
			no ->
			    CollectorData#collector_data.state
		    end,
	    UpdatedCollectorData = CollectorData#collector_data{state=State},
	    log("[~p] collector has entered the state: ~p~n", [?MODULE, UpdatedCollectorData#collector_data.state]),
            VtpPid ! {receive_decision, CollectorData#collector_data.decision, collector},
            collector(Collectors, UpdatedCollectorData);
        {commit, VtpPid} ->
	    FsmPid = clc:init_fsm(CollectorData#collector_data.state),
	    State = case CollectorData#collector_data.action of
			redeem ->
			    clc:redeem(FsmPid, CollectorData#collector_data.state)
		    end,
	    UpdatedCollectorData = CollectorData#collector_data{state=State},
	    log("[~p] collector has entered the state: ~p~n", [?MODULE, UpdatedCollectorData#collector_data.state]),
            log_final_state(commit,"Collector"),
            VtpPid ! {acknowledgement};
        {abort, VtpPid} ->
	    FsmPid = clc:init_fsm(CollectorData#collector_data.state),
	    State = clc:abort(FsmPid, CollectorData#collector_data.state),
	    UpdatedCollectorData = CollectorData#collector_data{state=State},
	    log("[~p] collector has entered the state: ~p~n", [?MODULE, UpdatedCollectorData#collector_data.state]),
            log_final_state(commit,"Collector"),
            VtpPid ! {acknowledgement}
    end.
