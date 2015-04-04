# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, you can access it online at
# http://www.gnu.org/licenses/gpl-2.0.html.
#
# Copyright IBM Corporation, 2015
#
# Author: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

PROGRAMS = litmus ptxroute ptxrouteUP stackptxroute stackroute stackrouteUP

all: $(PROGRAMS)

litmus: litmus.c rcu.h fake.h Makefile 
	cc -Wall -I . -g -o litmus litmus.c -lpthread
	@if ./litmus ; then echo SUCCESSFUL ; else echo FAILED ; fi

ptxroute: ptxroute.c rcu.h fake.h Makefile 
	cc -Wall -I . -g -o ptxroute ptxroute.c -lpthread
	cc -Wall -I . -g -DDYNAMIC -o ptxrouteDYN ptxroute.c -lpthread
	@if ./ptxroute && ./ptxrouteDYN ; then echo SUCCESSFUL ; else echo FAILED ; fi

ptxrouteUP: ptxrouteUP.c rcu.h fake.h Makefile 
	cc -Wall -I . -g -o ptxrouteUP ptxrouteUP.c -lpthread
	cc -Wall -I . -g -DDYNAMIC -o ptxrouteUPDYN ptxrouteUP.c -lpthread
	@if ./ptxrouteUP && ./ptxrouteUPDYN ; then echo SUCCESSFUL ; else echo FAILED ; fi

stackptxroute: stackptxroute.c rcu.h fake.h Makefile 
	cc -Wall -I . -g -o stackptxroute stackptxroute.c -lpthread
	cc -Wall -I . -g -DDYNAMIC -o stackptxrouteDYN stackptxroute.c -lpthread
	@if ./stackptxroute && ./stackptxrouteDYN ; then echo SUCCESSFUL ; else echo FAILED ; fi

stackroute: stackroute.c rcu.h fake.h Makefile 
	cc -Wall -I . -g -o stackroute stackroute.c -lpthread
	cc -Wall -I . -g -DDYNAMIC -o stackrouteDYN stackroute.c -lpthread
	@if ./stackroute && ./stackrouteDYN ; then echo SUCCESSFUL ; else echo FAILED ; fi

stackrouteUP: stackrouteUP.c rcu.h fake.h Makefile 
	cc -Wall -I . -g -o stackrouteUP stackrouteUP.c -lpthread
	cc -Wall -I . -g -DDYNAMIC -o stackrouteUPDYN stackrouteUP.c -lpthread
	@if ./stackrouteUP && ./stackrouteUPDYN ; then echo SUCCESSFUL ; else echo FAILED ; fi
