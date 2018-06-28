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
%%% This module implements a simple screen logger used for debugging
%%% purposes
%%% --------------------------------------------------------------------
-module(logger).

-export([log_final_state/2,log/1,log/2]).

log(String) ->
    log(String, []).

log(String, Arguments) ->
    io:fwrite(
      string:join(
        [
            "~p - ",
            String,
            "~n"
        ],
        ""
      ),
      lists:append(
        [self()],
        Arguments
      )
    ).

log_final_state(commit, Sender) ->
    log("Commit! by " ++ Sender ++ "~n");
log_final_state(abort, Sender) ->
    log("ABORT! by " ++ Sender ++ "~n").
