# LIFELINE: preliminary evidence

This archive contains the preliminary evidence cited in the ERC proposal LIFELINE
(PI: Yusuke Izawa, Tokyo Metropolitan University). It has two independent parts.

- `aggregation-core/` (cited as `izawa2026artifact`). For a pipeline that sums contributions
  from peers, the state a runtime must retain is derived from the declared policies alone.
  The derivation is compared with an exhaustive ground truth, certified, and verified by an
  independent checker. Lean 4 proofs cover the order-independent case without a length bound.
- `leave-transition/` (cited as `izawa2026leave`). A 7-line change rule `leave(p, reason)` is
  implemented in MetaTensor, a meta-tracing tensor runtime built on PyPy. The rule is ordinary
  interpreter code and is therefore compiled by the meta-tracer. All reported numbers are
  re-derived from the archived data of one GPU run.

## Claims and evidence

| Claim in the proposal | File | Command or data | Expected output |
|---|---|---|---|
| The retained state is derived from the policies and is sound and complete for histories of up to 3 steps | `aggregation-core/congruence.py` | `python3 congruence.py` | `index = 79` (order-dependent), `index = 9` (order-independent) |
| An independent checker accepts the certificates | `aggregation-core/checker.py` | `python3 certify.py && python3 checker.py` | `10 ACCEPT, 0 REJECT, 30152 total obligations` |
| The checker rejects tampered certificates | `aggregation-core/negative_controls.py` | `python3 negative_controls.py` | `all rejected` |
| For P1/Pi_base, the per-peer sums are sufficient and irredundant for any history length | `aggregation-core/lean/` | `lake build`, `lake env lean Axioms.lean` | build succeeds, axiom `propext` only |
| `leave(p, reason)` has 7 lines and uses only the abstract interface | `leave-transition/rederive.py` | `audit_rules.py`, `count_lines.py` | audit passes, leaky copy rejected, 7 lines |
| The meta-tracer compiles the rule | `leave-transition/rederive.py` | `leave.tsv` | traces on all 5 histories, none with the JIT disabled |
| The results agree with an independent checker on 5 histories, and 2 faulty variants are detected | `leave-transition/rederive.py` | `data.tar.gz` | all pass, both variants detected on `h2` |
| 1.16 GPU kernel launches per step, against 5.00 for a hand-written adapter | `leave-transition/rederive.py` | `leave.tsv`, `leave_perf.tsv` | `1.160`, `5.000` |
| 21 lines decide what to retain, 139 lines exist only for the change, and the adapter needs 27 | `leave-transition/linecount_roles.tsv` | `rederive.py` | `21`, `139`, `27` |

## Remarks

The counts 79 and 9 are the numbers of history classes found by an exhaustive search over all
259 histories of up to 3 steps and all continuations of up to 2 events. The search does not
use the derivation. A hand-written summary can attain the same counts; the claim is that the
derivation attains them from the declared policies alone. At 4 steps `certify.py` refuses the
order-dependent case.

The Lean proofs concern the order-independent case only. For P1/Pi_base they show that the
per-peer sums mod 3 suffice for retain and for every revoke(S), and that neither the total sum
nor a single per-peer sum suffices, for histories and continuations of any length
(`perPeer_enough`, `total_separates`, `total_not_enough`, `dropA_not_enough`, `dropB_not_enough`).
`perPeer_classes_L3` confirms the 9 classes at 3 steps. `no_change_is_compiler_correctness`
holds by `Iff.rfl` and only checks that Definition 1 is modelled consistently. The derivation
itself and the order-dependent 79-class case are not proved.

The evidence for meta-tracer compilation consists of the loop and bridge counts in the archived
run; observing them again requires a PyPy build. Both faulty variants are detected on `h2`, the
only history that exercises revoke. `count_lines.py` yields only the raw totals 246 and 47. The
figures 21, 139 and 27 follow from the author's per-line classification in `linecount_roles.tsv`.

## Reproduction

```
bash reproduce.sh
```

Requirements: Python 3.12 or later and bash 5, standard library only, no network or GPU.
Running time is about 15 s. The script reruns `aggregation-core/` from scratch, confirms that
`certify.py` regenerates `certs/` byte for byte, verifies the archived TensorPyPy files against
their git blobs, and re-derives every number in `leave-transition/`. It exits non-zero on any
difference. Last verified on 2026-10-12 with Python 3.14.8.

`reproduce.sh` does not build the Lean proofs. These require Lean 4 v4.34.1 (available through
elan); run `lake build` and `lake env lean Axioms.lean` in `aggregation-core/lean/`.

## Scope and limitations

- The Python tools in `aggregation-core/` are exhaustive only over 2 peers, values mod 3 and histories of up to 3 steps. The Lean proofs remove the length bound for P1/Pi_base only and do not cover the derivation.
- The checker reads the pipeline and the policy set from the instance name. A certificate cannot shrink either, but the name itself is trusted.
- The numbers in `leave-transition/` come from one run on one NVIDIA RTX 3090. They are re-derived from the archived data, not re-measured.
- The adapter is an application-level baseline, not a tuned hand-written transition.
- `rederive.py` checks that `linecount_roles.tsv` covers exactly the counted lines and matches the source text. The roles themselves are a judgement.

## Source and license

The TensorPyPy sources are at https://github.com/3tty0n/tensorpypy, commit
`ec9f5fb09781a18916b4df5a3ef7249b64ee71b2`. Every source file under `leave-transition/tensorpypy/`
is byte-identical to that commit, as `reproduce.sh` verifies. The run data under
`benchmark/results/` are not part of that commit; `leave-transition/README.md` gives details.

Upstream PyPy files are under the PyPy MIT license (`leave-transition/tensorpypy/LICENSE`).
The TensorPyPy and MetaTensor additions, including `benchmark/`, are under the MIT license in
`leave-transition/tensorpypy/LICENSE-tensorpypy`. All other files are under `LICENSE`.
