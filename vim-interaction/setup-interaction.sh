#!/bin/bash

PIPE_FILENAME=/tmp/hol_light
OUTPUT_REDIRECTION_FILENAME=hol-light-redirected-output.txt
KILL_SIGNAL_SENDER=send-INT-signal-to-ocaml-background-process.sh
HOL_LIGHT_HOME=~/Developer/working-copies/hol_light/

mkfifo $PIPE_FILENAME
cd $HOL_LIGHT_HOME
nohup tail -s 0.1 -f $PIPE_FILENAME | ocaml > $OUTPUT_REDIRECTION_FILENAME & 
OCAML_PID=$!
echo "kill -SIGINT ${OCAML_PID}" > $KILL_SIGNAL_SENDER
chmod +x $KILL_SIGNAL_SENDER
echo "#use \"hol.ml\";;" > $PIPE_FILENAME
tail pid=$OCAML_PID -f $OUTPUT_REDIRECTION_FILENAME
