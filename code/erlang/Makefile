## --------------------------------------------------------------------
## Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.
##
## Released under the terms of the GNU Affero General Public License
## v3.0. See: file LICENSE that came with this software for details.
##
## This file contains Intellectual Property that belongs to
## Backyard Innovations Pte Ltd., Singapore.
##
## Author: Santhosh Raju    <santhosh@byisystems.com>
## --------------------------------------------------------------------
EBIN	 =	ebin
GEN	 = 	beam
SCRIPTS  = 	scripts

.PHONY: all deps compile clean distclean

all: deps compile

compile: deps
	./rebar compile

deps:
	test -d ebin || mkdir $(EBIN)
	cp -p $(SCRIPTS)/*.sh $(EBIN)

clean:
	./rebar clean
	rm -fr .rebar/
	rm -fr $(EBIN)
	rm -fr *.dump $(EBIN)/*.dump

distclean: clean
	rm -f $(SCRIPTS)/*.$(GEN)
