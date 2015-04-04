#!/bin/sh
#
# Run the tests under CBMC and complain if they don't go as expected.
#
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

# runfailure args
#
# Run CBMC on the specified file with the specified definitions, with
# the expectation that verification will fail
runfailure () {
	echo ' --- ' cbmc -I . -DCBMC $*
	echo ' --- Expecting verification failure'
	if cbmc -I . -DCBMC $*
	then
		echo ' ^^^ Unexpected successful verification'
		failure=1
	fi
}

# runsuccess args
#
# Run CBMC on the specified file with the specified definitions, with
# the expectation that verification will succeed.
runsuccess () {
	echo ' --- ' cbmc -I . -DCBMC $*
	echo ' --- Expecting successful verification'
	if cbmc -I . -DCBMC $*
	then
		:
	else
		echo ' ^^^ Unexpected verification failure'
		failure=1
	fi
}

runsuccess litmus.c
runfailure -DFORCE_FAILURE_GP litmus.c
runfailure -DFORCE_FAILURE_READER litmus.c

runsuccess --unwind 3 ptxroute.c
runfailure --unwind 3 -DFORCE_FAILURE_1 ptxroute.c
runfailure --unwind 3 -DFORCE_FAILURE_2 ptxroute.c
runfailure --unwind 3 -DFORCE_FAILURE_3 ptxroute.c

runsuccess --unwind 3 ptxrouteUP.c
runsuccess --unwind 3 -DDYNAMIC ptxrouteUP.c
runfailure --unwind 3 -DFORCE_FAILURE_1 ptxrouteUP.c
runfailure --unwind 3 -DFORCE_FAILURE_2 ptxrouteUP.c

runsuccess --unwind 3 stackptxroute.c
runfailure --unwind 3 -DFORCE_FAILURE_1 stackptxroute.c
runfailure --unwind 3 -DFORCE_FAILURE_2 stackptxroute.c
runfailure --unwind 3 -DFORCE_FAILURE_3 stackptxroute.c

runsuccess --unwind 3 stackroute.c
runfailure --unwind 3 -DFORCE_FAILURE_1 stackroute.c
runfailure --unwind 3 -DFORCE_FAILURE_2 stackroute.c

runsuccess --unwind 3 stackrouteUP.c
runsuccess --unwind 3 -DDYNAMIC stackrouteUP.c
runfailure --unwind 3 -DFORCE_FAILURE_1 stackrouteUP.c

if test -n "$failure"
then
	echo ' --- ' UNEXPECTED VERIFICATION RESULTS
	exit 1
else
	echo ' --- ' Verification proceeded as expected
	exit 0
fi
