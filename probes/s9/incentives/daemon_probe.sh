#!/bin/sh
# S9 incentives probe: a step's double-forked daemon outlives the step? It sleeps 3 s, then writes
# daemon.txt into the step directory. Run inside bwrap-landrun.sh --minimal-root; afterwards the
# caller waits 5 s and checks whether daemon.txt appeared (it must not: PID namespace, die-with-parent).
( setsid sh -c 'sleep 3; echo alive > daemon.txt' & ) ; echo "step exits now"
