## Hybrid Coq/`minuska` benchmarks

To get some statistics about the languages defined in [../languages-in-coq](../languages-in-coq) converted into Coq and executed inside Coq, run:
```sh
nix develop '.#bench-hybrid' --command ./test.sh
```
The output contains lines like
```
coqc testCount7.v
Finished transaction in 1.814 secs (1.806u,0.002s) (successful)
2.45
coqc testTC100.v
Finished transaction in 0.094 secs (0.093u,0.s) (successful)
0.68
```
where each three lines correspond to one benchmark: the first one the three contains the name of the benchmark, the second line the time required for Coq to execute the corresponding `Compute` command, and the third line is the execution time as measured by the GNU `time` utility.
This suite contains only two kind of benchmarks. The ones named `testCount${N}` run the `sum-to-${N}` program in the IMP language defined in [../languages/imp](../languages/imp), but do so inside Coq. The ones named `testTC${N}` run the `two-counters` language ([../languages/two-counters](../languages/two-counters)) on input `${N}`.

