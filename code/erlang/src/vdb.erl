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
%%% This module implements a mock database handler for vouchers used
%%% for testing purposes. This should *NOT* be there in the production
%%% code.
%%% --------------------------------------------------------------------
-module(vdb).

-export([generate/1,getv/1]).

-import(logger,[log/1,log/2,log_final_state/2]). % @todo Use a proper logging framework
-import(lists, [last/1]).

-record(voucher_data, {id, state, origin, owner}).

generate(IssuerId) ->
    Id = rand:uniform(300),
    #voucher_data{id=Id, state=initialize, origin=IssuerId, owner=nil}.

getv(VoucherId) ->
    last([VD || VD <- init_vouchers(), VD#voucher_data.id == VoucherId]).

init_vouchers() ->
    V01 = #voucher_data{id=501, state=valid, origin="i1", owner="h1"},
    V02 = #voucher_data{id=502, state=valid, origin="i2", owner="h2"},
    V03 = #voucher_data{id=601, state=redeemed, origin="i2", owner="c1"},
    V04 = #voucher_data{id=701, state=cancelled, origin="i1", owner="h1"},
    [ V01, V02, V03, V04 ].
