A7-M3 probe: the gate (and the badge) must run on the build that the comparator verified.
SwitchSol.lean elaborates differently in the comparator's build (honest) and in the gate's rebuild
(submission.vk = 1337 and a false `certified` added under debug.skipKernelTC); it tells the two apart by
the file WORK/cmp-build.sha256 that the harness writes between them.
Driver: tests/pipeline/bindproj.sh (CI step 9). Honest.lean is the positive control.
