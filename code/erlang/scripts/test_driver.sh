#!/bin/sh
# --------------------------------------------------------------------
# Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.
#
# Released under the terms of the GNU Affero General Public License
# v3.0. See: file LICENSE that came with this software for details.
#
# This file contains Intellectual Property that belongs to
# Backyard Innovations Pte Ltd., Singapore.
#
# Author: Santhosh Raju    <santhosh@byisystems.com>
# --------------------------------------------------------------------
OS_TYPE=$(uname -o)
DEPS="deps/*/ebin"
EBIN="ebin"

if [ "$OS_TYPE" = "Cygwin" ]
then
    ERL="werl"
else
    ERL="erl"
fi

${ERL} -pa ${EBIN} -pa ${DEPS} -pa ..${DEPS} -boot start -s test_driver start
