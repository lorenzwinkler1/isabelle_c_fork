# Jacques-Henri Jourdan, Inria Paris
# François Pottier, Inria Paris
#
# Copyright (c) 2016-2017, Inria
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of Inria nor the
#       names of its contributors may be used to endorse or promote products
#       derived from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL INRIA BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

.PHONY: all test clean realclean

MENHIR := menhir --no-stdlib --unused-token IMAGINARY -lg 1 -la 1 -v

all:
	ocamlbuild -menhir "$(MENHIR)" main.native
	mv main.native parse

test: all
	cram tests/tests.t

clean:
	rm -rf _build parse
	rm -f parser.output parser.tab.c

parser.y: parser.mly
	rm -f $@

	echo /\* > $@
	echo Jacques-Henri Jourdan, Inria Paris >>$@
	echo François Pottier, Inria Paris >>$@
	echo >>$@
	cat LICENSE >> $@
	echo \*/ >> $@
	echo >>$@

	$(MENHIR) --only-preprocess-uu $< >> $@
	bison -r all $@

realclean: clean
	rm -f parser.y
