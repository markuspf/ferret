#
# ferret: 
#
# This file is part of the build system of a GAP kernel extension.
# Requires automake.
#

## Configuration options

CHECK=0

ifdef TIMING
timingflag = -DENABLE_TIMING
else
timingflag =
endif

ifneq ($(CHECK),0)
checkflag = $(DEBUGFLAGS) -DDEBUG_LEVEL=$(CHECK)
else
checkflag = -DDEBUG_LEVEL=0
endif

ifndef OPT
OPT = -O3
endif

ifdef PRINT
printflag = -DDEBUG_PRINT_LEVEL=$(PRINT)
else
printflag =
endif

MYCFLAGS=-std=gnu++11 -Wall -Wextra -Wno-missing-field-initializers -g -IYAPB++/source -Igap_cpp_headers

##############

ACLOCAL_AMFLAGS = -I m4

BINARCHDIR = bin/$(GAPARCH)
GAPINSTALLLIB = $(BINARCHDIR)/ferret.so

lib_LTLIBRARIES = ferret.la

ferret_la_SOURCES = src/ferret.cc
ferret_la_CPPFLAGS = $(GAP_CPPFLAGS) $(MYCFLAGS) $(timingflag) $(checkflag) $(OPT) -DCONFIG_H
ferret_la_LDFLAGS = -module -avoid-version
if SYS_IS_CYGWIN
ferret_la_LDFLAGS += -no-undefined -version-info 0:0:0 
ferret_la_LDFLAGS += -Wl,$(GAPROOT)/bin/$(GAPARCH)/gap.dll
endif



all-local: $(GAPINSTALLLIB)

$(GAPINSTALLLIB): ferret.la
	$(mkdir_p) $(BINARCHDIR)
if SYS_IS_CYGWIN
	cp .libs/ferret.dll $(GAPINSTALLLIB)
else
	cp .libs/ferret.so $(GAPINSTALLLIB)
endif

clean-local:
	rm -f $(GAPINSTALLLIB)
	rm -f symmetry_detect

distclean-local:
	rm -rf bin/*

doc:
	($(GAPROOT)/bin/gap.sh -A makedoc.g)

symmetry_detect : .FORCE
	cxx $(MYCFLAGS) YAPB++/simple_graph/symmetry_detect.cc YAPB++/simple_graph/symmetry_parse.cc  YAPB++/simple_graph/gason/gason.cpp  YAPB++/simple_graph/simple_graph.cc YAPB++/simple_graph/simple_parser.cc $(timingflag) $(checkflag) $(OPT) $(printflag) -I YAPB++/source -o symmetry_detect