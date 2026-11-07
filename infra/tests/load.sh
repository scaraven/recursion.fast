# A light slot's load for the frequency sweep (rf-test light1 load.sh --tar core.tar; DUR is
# prepended by freq-sweep.sh): the calibration workload on the VM's one vCPU (AVX2 BLAKE2s,
# carry-less multiplication and a 256 MiB sweep) in a loop for DUR seconds.
cd ~ && gcc -O2 -pthread -o calib core/harness/tools/calib.c || exit 1
end=$((SECONDS + DUR))
n=0; while ((SECONDS < end)); do ./calib 1 64 >/dev/null; n=$((n + 1)); done
echo "load: $n calib runs in $DUR s"
