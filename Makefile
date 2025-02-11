#########################################################################
#                                   Ott                                  #
#                                                                        #
#        Peter Sewell, Computer Laboratory, University of Cambridge      #
#      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     #
#                                                                        #
#  Copyright 2005-2011                                                   #
#                                                                        #
#  Redistribution and use in source and binary forms, with or without    #
#  modification, are permitted provided that the following conditions    #
#  are met:                                                              #
#  1. Redistributions of source code must retain the above copyright     #
#  notice, this list of conditions and the following disclaimer.         #
#  2. Redistributions in binary form must reproduce the above copyright  #
#  notice, this list of conditions and the following disclaimer in the   #
#  documentation and/or other materials provided with the distribution.  #
#  3. The names of the authors may not be used to endorse or promote     #
#  products derived from this software without specific prior written    #
#  permission.                                                           #
#                                                                        #
#  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    #
#  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     #
#  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    #
#  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       #
#  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    #
#  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     #
#  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         #
#  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  #
#  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       #
#  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   #
#  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         #
##########################################################################

# make world #############################################################

world:
	cd src; $(MAKE) install

world.byt:
	cd src; $(MAKE) install.byt

# cleanup ################################################################

clean:
	cd src; $(MAKE) clean
	rm -f *~
	rm -f ott.install

# ott.install file ######################################################

ott.install : built_doc/*
	cp ott.install.nodoc ott.install
	echo "doc : [" >> ott.install
	echo "\"README.md\" { \"README.md\" }" >> ott.install
	echo "\"LICENCE\" { \"LICENSE\" }" >> ott.install
	echo "\"built_doc/top2.pdf\" { \"doc/ott_manual.pdf\" }" >> ott.install
	echo "\"built_doc/top2.html\" { \"doc/ott_manual.html\" }" >> ott.install
	echo $(patsubst %, "\"%\"", $(wildcard built_doc/*.png)) >> ott.install
	echo "]" >> ott.install

# tests ##################################################################

LATEX		= latex
DVIPS		= dvips

DST_DIR = output
output:
	@mkdir -p $(DST_DIR)

outclean:
	rm -R $(DST_DIR)/*

# normal case, e.g. "make tests/test8.out"


l23_deps = tests/l23.ott tests/l23_typing.ott
# l23_deps = tests/l23.ott 
tests/l23.out: $(l23_deps)
	ott -merge true -o $(DST_DIR)/l23.thy -o $(DST_DIR)/l23.v -o $(DST_DIR)/l23Script.sml -o $(DST_DIR)/l23.tex -o $(DST_DIR)/l23.ml 		\
					$(l23_deps) 		\

# && ($(LATEX) $(DST_DIR)/l23; $(DVIPS) out -o)





%.out: %.ott 
	ott   							\
                -o $(DST_DIR)/out.thy -o $(DST_DIR)/out.v -o $(DST_DIR)/outScript.sml 	\
	        -o $(DST_DIR)/out.tex 						\
                $<                                                      \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

%.tex.out: %.ott
	ott   							\
	        -o $(DST_DIR)/out.tex 						\
                $<                                                      \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

%.coq.out: %.ott
	ott   							\
                -o $(DST_DIR)/out.v  						\
	        -o $(DST_DIR)/out.tex 						\
                $<                                                      \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

%.hol.out: %.ott
	ott   							\
                -o $(DST_DIR)/outScript.sml 					\
	        -o $(DST_DIR)/out.tex 						\
                $<                                                      \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

%.isa.out: %.ott
	ott   							\
                -o $(DST_DIR)/out.thy 					\
	        -o $(DST_DIR)/out.tex 						\
                $<                                                      \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

# test10 special cases 

test10: tests/test10.ott
	ott   							\
                -o $(DST_DIR)/out.thy -o $(DST_DIR)/out.v -o $(DST_DIR)/outScript.sml 	\
	        -o $(DST_DIR)/out.tex 						\
	        -parse ":user_syntax: :user_syntax__t: :concrete: \x1'.x1'"  \
	        -parse ":user_syntax: :concrete: \x1'.x1'"  		\
	        -parse ":user_syntax: \x1'.x1'"  			\
	        -parse ":concrete_t:\x1'.x1'"                      	\
                tests/test10.ott                           		\
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

test10st_halves: tests/test10st_first_half.ott tests/test10st_second_half.ott
	ott  -o $(DST_DIR)/out.thy -o $(DST_DIR)/out.v -o $(DST_DIR)/out.tex 		\
	         -o $(DST_DIR)/outScript.sml 					\
                 tests/test10st_first_half.ott 			 	\
                 tests/test10st_second_half.ott    			\
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

test10_isasyn: tests/test10_isasyn.ott
	ott -colour true -showraw false  				\
                -o $(DST_DIR)/out.thy -o $(DST_DIR)/out.v -o $(DST_DIR)/out.tex 		\
                -isa_syntax true 					\
	        -tex_show_meta true                                     \
                tests/test10_isasyn.ott                              	\
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

# test 7 special case - ott as a munger

test7afilter: tests/test7b.ott tests/test7t.mng
	ott  -o $(DST_DIR)/out.sty 						\
	       -tex_show_meta false                                     \
	       -tex_wrap false                                          \
	       -tex_name_prefix	ott					\
	       -tex_filter tests/test7t.mng out.tex        		\
               tests/test7b.ott 			      		\
        && ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

# TAPL examples

SYS_BOOL = 				\
  examples/tapl/common.ott 		\
  examples/tapl/bool.ott

SYS_ARITH = 				\
  examples/tapl/nat.ott 		\
  $(SYS_BOOL) 

SYS_UNTYPED = 				\
  examples/tapl/common.ott 		\
  examples/tapl/bool.ott

SYS_PURESIMPLE = 			\
  examples/tapl/common.ott 		\
  examples/tapl/common_typing.ott 	\
  examples/tapl/arrow_typing.ott

SYS_TYBOOL = 				\
  examples/tapl/bool.ott 		\
  examples/tapl/bool_typing.ott 	\
  $(SYS_PURESIMPLE)

SYS_SORTOFFULLSIMPLE = 			\
  examples/tapl/common.ott        	\
  examples/tapl/common_typing.ott 	\
  examples/tapl/common_labels.ott 	\
  examples/tapl/common_index.ott 	\
  examples/tapl/arrow_typing.ott  	\
  examples/tapl/basety.ott  	     	\
  examples/tapl/bool.ott  	     	\
  examples/tapl/bool_typing.ott   	\
  examples/tapl/nat.ott	     	\
  examples/tapl/nat_typing.ott    	\
  examples/tapl/unit.ott	     	\
  examples/tapl/seq.ott	     	\
  examples/tapl/ascribe.ott       	\
  examples/tapl/inert.ott         	\
  examples/tapl/let.ott           	\
  examples/tapl/sum.ott        	\
  examples/tapl/variant.ott        	\
  examples/tapl/product.ott       	\
  examples/tapl/tuple.ott        	\
  examples/tapl/record.ott        	\
  examples/tapl/fix.ott  	     
# examples/tapl/arrow.ott  	     	\

SYS_ROUGHLYFULLSIMPLE = \
  examples/tapl/common.ott \
  examples/tapl/common_index.ott \
  examples/tapl/common_labels.ott \
  examples/tapl/common_typing.ott \
  examples/tapl/bool.ott \
  examples/tapl/bool_typing.ott \
  examples/tapl/nat.ott \
  examples/tapl/nat_typing.ott \
  examples/tapl/arrow_typing.ott \
  examples/tapl/basety.ott \
  examples/tapl/unit.ott \
  examples/tapl/seq.ott \
  examples/tapl/ascribe.ott \
  examples/tapl/let.ott \
  examples/tapl/product.ott \
  examples/tapl/sum.ott \
  examples/tapl/fix.ott \
  examples/tapl/tuple.ott \
  examples/tapl/variant.ott
# examples/tapl/record.ott

SYS_TUPLE = 				\
  examples/tapl/common.ott        	\
  examples/tapl/common_typing.ott 	\
  examples/tapl/common_index.ott 	\
  examples/tapl/unit.ott	     	\
  examples/tapl/tuple.ott        
# examples/tapl/arrow.ott  	     	\

SYS_PURESUB = 				\
  examples/tapl/common.ott        	\
  examples/tapl/common_typing.ott 	\
  examples/tapl/arrow_typing.ott  	\
  examples/tapl/sub_arrow.ott     	\
  examples/tapl/top.ott  	     

SYS_PURERCDSUB = $(SYS_PURESUB) 	\
  examples/tapl/common_labels.ott 	\
  examples/tapl/common_index.ott 	\
  examples/tapl/record.ott        	\
  examples/tapl/sub_record.ott        

sys-bool: $(SYS_BOOL) 
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_BOOL) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o) 

sys-arith: $(SYS_ARITH)
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_ARITH) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

sys-untyped: $(SYS_UNTYPED)
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_UNTYPED) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

sys-puresimple: $(SYS_PURESIMPLE)
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_PURESIMPLE) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

sys-tuple: $(SYS_TUPLE)
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_TUPLE) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

sys-tybool: $(SYS_TYBOOL)
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_TYBOOL) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

sys-sortoffullsimple: $(SYS_SORTOFFULLSIMPLE)
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_SORTOFFULLSIMPLE) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

sys-roughlyfullsimple: $(SYS_ROUGHLYFULLSIMPLE)
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_ROUGHLYFULLSIMPLE) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

sys-puresub: $(SYS_PURESUB)
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_PURESUB) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

sys-purercdsub: $(SYS_PURERCDSUB)
	ott -merge true -tex_show_meta false -o $(DST_DIR)/out.tex -o $(DST_DIR)/out.v -o $(DST_DIR)/out.thy -o $(DST_DIR)/outScript.sml $(SYS_PURERCDSUB) \
	&& ($(LATEX) $(DST_DIR)/out; $(DVIPS) out -o)

# Jenksin regression

jenkins:
	cd regression; \
          make run-jenkins
