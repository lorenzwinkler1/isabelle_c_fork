#!/bin/bash

 ###############################################################################
 # Isabelle/C
 #
 # Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 #
 # All rights reserved.
 #
 # Redistribution and use in source and binary forms, with or without
 # modification, are permitted provided that the following conditions are
 # met:
 #
 #     * Redistributions of source code must retain the above copyright
 #       notice, this list of conditions and the following disclaimer.
 #
 #     * Redistributions in binary form must reproduce the above
 #       copyright notice, this list of conditions and the following
 #       disclaimer in the documentation and/or other materials provided
 #       with the distribution.
 #
 #     * Neither the name of the copyright holders nor the names of its
 #       contributors may be used to endorse or promote products derived
 #       from this software without specific prior written permission.
 #
 # THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 # "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 # LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 # A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 # OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 # SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 # LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 # DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 # THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 # (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 # OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ###############################################################################

set -x
set -e

README_MD=README.md
README_HTML=README.html
SESSION=Isabelle_C_README

$ISABELLE_TOOL build -b -v -o browser_info -d . $SESSION
echo -e '<div class="source">\n\n``` {.source}' > $README_MD
pandoc -t markdown $ISABELLE_HOME_USER/browser_info/Unsorted/$SESSION/$README_HTML | grep -zo 'section.*' | head -n -4 >> $README_MD
echo -e '```\n\n</div>' >> $README_MD
git add $README_MD
git commit -m 'update the generated files'
