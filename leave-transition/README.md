# Leave transition in MetaTensor

MetaTensor is a meta-tracing tensor runtime built on PyPy. The change rule `leave(p, reason)`
(`rule_leave.py`, 7 lines) removes peer `p` from a group. The application declares for each
reason whether the uncommitted contributions of `p` are retained or revoked; in the archived run,
`preempt` retains and `fault` revokes. The rule is called from interpreter
code (`interp_group.py`), so the meta-tracer compiles it like any other interpreter code. This
directory archives a run of 2026-09-23 on one NVIDIA RTX 3090.

```
python3 rederive.py
```

`rederive.py` re-derives every number from the archived sources and data. It requires neither a
GPU nor a PyPy build.

## Histories

`check_leave.py` defines five histories: `h1` (B leaves after contributing, preempt), `h2` (B leaves
after contributing, fault, so its contribution is revoked), `h3` (B leaves before contributing,
fault), `h2post` (B faults after the step has committed) and `none` (no peer leaves). Each history
runs in three implementations: `ref` (interpreter only, JIT disabled), `motion` (the rule, JIT
enabled) and `adapter` (a hand-written application-level transition, `adapter_leave.py`).

## Numbers and their sources

| Number | Source |
|---|---|
| 7-line rule; the audit passes and a leaky control copy is rejected | `benchmark/eval/audit_rules.py`, `benchmark/motion/count_lines.py` |
| `motion` and `adapter` agree with the checker and with `ref` on all 5 histories | `benchmark/motion/check_leave.py` on `data.tar.gz` |
| Faulty variants `erase` and `late` are detected on `h2`, the only history that exercises revoke | same |
| Meta-tracer compilation: loops and bridges on every history, none with the JIT disabled | `leave.tsv`, columns `loops` and `bridges` (archived run; a PyPy build is needed to observe them again) |
| 1.16 versus 5.00 kernel launches per step | `leave.tsv` and `leave_perf.tsv` in `data.tar.gz` (n=65536, median of 10 runs, sync=0) |
| 246 / 47 raw lines | `count_lines.py` |
| 21 / 139 / 27 lines | the author's per-line classification in `linecount_roles.tsv` |

## Files

- `tensorpypy/` contains files from TensorPyPy (https://github.com/3tty0n/tensorpypy, commit `ec9f5fb09781a18916b4df5a3ef7249b64ee71b2`) at their paths in that tree. `SOURCES.txt` records the git blob of each file, and `reproduce.sh` verifies them. All source files are byte-identical to that commit.
- The run used an earlier, unpublished revision. Relative to it, the public commit trims comments and docstrings, renames `benchmark/paper/` to `benchmark/eval/` and rewrites `rule_leave.provenance` as a description of the audit. Ignoring comments and docstrings, the code of every archived Python file is unchanged and the shell scripts differ only in comments. There are two exceptions. `moduledef.py` registers further `interp_tensor` functions not used by the leave rule, and `audit_rules.py` prints reworded pass and fail messages. `rule_leave.py`, `adapter_leave.py` and `check_leave.py` are byte-identical to the revision used in the run. All numbers re-derive unchanged, and `linecount_roles.tsv` gives line numbers in the public files.
- The run data under `benchmark/results/rtx3090/motion-2026-09-23/` are not part of the public commit. The host name and home paths were removed from `machine.txt` and from the `.out` and `.log` files in `data.tar.gz`, and the result directory was renamed to `rtx3090`. One sentence referring to another evaluation run was removed from `summary.md`, and one line naming an unpublished commit from `summary.md` and `audit.log`. `summary.md` shows the audit messages of the earlier revision. The `.tsv` and `.jsonl` rows are unchanged. `SOURCES.txt` marks these files `run` and records the hash of the archived copy. They refer to `benchmark/paper/`, the path before the rename.
- `linecount_roles.tsv` assigns a role to every line that `count_lines.py` counts: `A` ordinary semantics, `B` application-level exposure, `C` test hooks, `D` present only for the change, `E` JIT annotations (`E:D` when serving the change). `sub=keep` marks the lines that decide what to retain.
- `rule_leave.provenance` describes the audit that `audit_rules.py` performs.
- `test/test_group_jit.py` checks guards and resume data. It requires a PyPy checkout and is not rerun here.
- `run_leave.sh` requires the full TensorPyPy tree and documents how the data were produced.

## Limitations

- One machine and one GPU. The timings in `summary.md` are not claimed beyond them.
- Every row was produced by binary `a99ad86b05e2`, built from the earlier revision plus uncommitted decode changes. A build of the public commit does not reproduce this hash.
- The roles in `linecount_roles.tsv` are a judgement by the author. `rederive.py` checks only that they cover exactly the counted lines and match the source text.
- Section 2 of `summary.md` and the figures are not cited in the proposal.
