# Aggregation core

This directory contains a small model of the aggregation core. Two peers, A and B, send
contributions with values in Z/3, which are summed. A pipeline combines split, aggregation,
in-place update and fusion, and a peer may leave. Each policy is declared as a sum over a filter
on peer and revision (the 1-indexed position of an event in the history). From these declarations
alone, `congruence.py` derives the state to retain: the coarsest partition of histories that every
admissible continuation and policy can still distinguish.

## Definitions

- **Pipelines.** P1: split, aggregation, in-place add, fusion. P2: source, layout, aggregation.
  P1': P1 with in-place add replaced by overwrite, a deliberately faulty local rule.
- **Policy sets.** `Pi_base`: retain (sum of all values) and revoke(S) (sum excluding the peers in S).
  `Pi_hist`: `Pi_base` plus the order-dependent policies `after_1` and `after_2` (sum of the first
  r events).
- **Universe.** Histories of up to `L` events and continuations of up to 2 events.

## Files

| File | Role |
|---|---|
| `congruence.py` | The derivation and a brute-force ground truth independent of it. Ends with `assert`s. |
| `certify.py` | Runs the derivation per instance and writes a certificate to `certs/`, or a refusal with a witness. |
| `checker.py` | Checks certificates. Imports neither `congruence.py` nor `certify.py`. |
| `negative_controls.py` | Tampers with certificates and confirms that the checker rejects them. |
| `lean/` | Lean 4 proofs for P1/Pi_base without a length bound (see `lean/README.md`). |

## Usage

```
python3 congruence.py        # about 9 s
python3 certify.py           # about 1.5 s, regenerates certs/ byte for byte
python3 checker.py           # about 0.7 s
python3 negative_controls.py
```

## Results

| `certs/` file | Instance | Result | Classes |
|---|---|---|---:|
| `P1_Pi_base_L3` | P1 / Pi_base, L=3 | certified | 9 |
| `P1_Pi_base_L4` | P1 / Pi_base, L=4 | certified | 9 |
| `P1_Pi_hist_L3` | P1 / Pi_hist, L=3 | certified | 79 |
| `P2_Pi_base_L3` | P2 / Pi_base, L=3 | certified | 9 |
| `P1_ThreePeer_Pi_base_L2` | P1 / Pi_base, 3 peers, L=2 | certified | 19 |
| `P1_Pi_hist3_L3` | P1 / after_1..3, L=3 | certified | 100 |
| `P1_Pi_hist_L4` | P1 / Pi_hist, L=4 | refused: no field covers an atom | |
| `P1prime_overwrite_Pi_base_L3` | P1' / Pi_base, L=3 | refused: no field covers an atom | |
| `P1_Pi_hist_L3_vcOFF` | P1 / Pi_hist, version check disabled | refused: atom not recoverable | |
| `Pi_ext_first_peer_wins_L3` | Pi_hist + first_peer_wins, L=3 | refused: not a declared filter | |

`checker.py` accepts all 10 certificates. For a certified instance it requires a separating
continuation for every pair of classes. For a refusal it reproduces the counterexample.

## Limitations

- The results are exhaustive over this universe only (259 histories at L=3). No claim is made for more peers, values or steps, except that `lean/` proves the P1/Pi_base result for any number of steps.
- Exactness requires every retained atom to lie in the span of the declared filters over GF(3). `congruence.py` checks and reports this condition; it holds for `Pi_hist`.
- `first_peer_wins` depends on event order in a way that no fixed filter expresses. With it the ground truth grows from 79 to 133 classes and the derivation is unsound; `congruence.py` prints the witness.
- P1/Pi_hist at L=4 is refused because the even-position stream of the split then carries positions 2 and 4, so no field isolates revision 2.
- The checker reads the pipeline and the policy set from the instance name, so a certificate cannot omit a policy. The name itself is trusted.
