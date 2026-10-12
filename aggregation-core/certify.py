#!/usr/bin/env python3
"""Certifying algorithm. For each instance it writes a soundness and completeness
certificate to certs/, or refuses and names the failed obligation with a witness.
"""
import itertools
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import congruence as C

OUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'certs')

RECIPE_TAGS = {
    'acc_a0': 'subtract_tail_sum',
}


# Ground-truth atom semantics. checker.py reimplements these independently.

def peer_atom_true(h, peer, vmod):
    total = 0
    for p, v in h:
        if p == peer:
            total = (total + v) % vmod
    return total


def rev_atom_true(h, lo, hi, vmod):
    count, total = 0, 0
    for i, (p, v) in enumerate(h, 1):
        if i >= lo and (hi is None or i <= hi):
            count += 1
            total = (total + v) % vmod
    return (count, total)


def joint_atom_true(h, peer, lo, hi, vmod):
    count, total = 0, 0
    for i, (p, v) in enumerate(h, 1):
        if p == peer and i >= lo and (hi is None or i <= hi):
            count += 1
            total = (total + v) % vmod
    return (count, total)


def revclass_bounds(cid, classes):
    for c, lo, hi in classes:
        if c == cid:
            return lo, hi
    raise KeyError(cid)


def atom_id_of(req):
    if req[0] == 'peer':
        return 'peer:%s' % req[1]
    if req[0] == 'rev':
        return 'rev:%s' % req[1]
    return 'joint:%s:%s' % (req[1], req[2])


def atom_true_value(req, classes, h, vmod):
    kind = req[0]
    if kind == 'peer':
        return peer_atom_true(h, req[1], vmod)
    if kind == 'rev':
        lo, hi = revclass_bounds(req[1], classes)
        return rev_atom_true(h, lo, hi, vmod)
    lo, hi = revclass_bounds(req[2], classes)
    return joint_atom_true(h, req[1], lo, hi, vmod)


# Soundness evidence: per required field, how erasure is survived.

def soundness_evidence(pipeline, field_req, version_check, histories):
    erased_by = {}
    for st in pipeline:
        for d in st.erases:
            erased_by[d] = st
    evidence = []
    for d in sorted(f for f in field_req if f is not None):
        st = erased_by.get(d)
        if st is None:
            evidence.append({'field': d, 'type': 'trivial', 'stage': None,
                              'map': 'identity (never erased)'})
            continue
        recipe = st.recipe.get(d)
        if version_check and recipe is not None:
            other_fields, _fn = recipe
            ok, bad = C.verify_recipe(pipeline, st, d, histories)
            evidence.append({
                'field': d, 'type': 'recipe', 'stage': st.name,
                'recipe_inputs': list(other_fields),
                'recipe_tag': RECIPE_TAGS.get(d, '?'),
                'version_check': 'ON',
                'recipe_verified_on_H_L': bool(ok),
                'recipe_counterexample': None if bad is None else [bad[0], bad[1], bad[2]],
            })
        elif version_check and recipe is None:
            evidence.append({'field': d, 'type': 'retain_explicit', 'stage': st.name,
                              'map': 'identity (retained literally after erasure point)'})
        else:
            evidence.append({'field': d, 'type': 'drop', 'stage': st.name,
                              'map': None, 'version_check': 'OFF'})
    return evidence


def evidence_reconstruct(evidence_by_field, pipeline, h):
    """Rebuild each required field by the recorded evidence branch, for the self-check."""
    ref = C.run(pipeline, h)
    out = {}
    for f, ev in evidence_by_field.items():
        if ev['type'] in ('trivial', 'retain_explicit'):
            out[f] = ref[f]
        elif ev['type'] == 'recipe':
            if f == 'acc_a0':
                acc_a = dict(ref['acc_a'])
                tail_sum = dict(ref['tail_sum'])
                out[f] = tuple(sorted((p, (acc_a[p] - tail_sum[p]) % C.VMOD) for p in acc_a))
            else:
                raise RuntimeError('unknown recipe tag for %r' % f)
        else:  # drop
            out[f] = None
    return out


def atom_from_fields(req, recon):
    kind, f = req[0], req[-1]
    val = recon[f]
    if val is None:
        return None
    if kind == 'peer':
        p = req[1]
        return sum(item[1] for item in val if item[0] == p) % C.VMOD
    if kind == 'rev':
        total = sum(item[1] for item in val) % C.VMOD
        return (len(val), total)
    p = req[1]
    items = [it for it in val if it[0] == p]
    total = sum(it[1] for it in items) % C.VMOD
    return (len(items), total)


# Policy factorisation: pi(h) as an explicit function of the atom vector.

def policy_factor_spec(decl, reqs, classes):
    """Atoms (by id, in `reqs` order) that a declared policy sums."""
    used = []
    if decl.peer_filter is not None and decl.rev_filter is None:
        for p in C.PEERS:
            if p in decl.peer_filter.exclude:
                continue
            for r in reqs:
                if r[0] == 'peer' and r[1] == p:
                    used.append(atom_id_of(r))
    elif decl.rev_filter is not None and decl.peer_filter is None:
        for cid, lo, hi in classes:
            if hi is not None and hi <= decl.rev_filter.max_rev:
                for r in reqs:
                    if r[0] == 'rev' and r[1] == cid:
                        used.append(atom_id_of(r))
    elif decl.peer_filter is not None and decl.rev_filter is not None:
        for p in C.PEERS:
            if p in decl.peer_filter.exclude:
                continue
            for cid, lo, hi in classes:
                if hi is not None and hi <= decl.rev_filter.max_rev:
                    for r in reqs:
                        if r[0] == 'joint' and r[1] == p and r[2] == cid:
                            used.append(atom_id_of(r))
    return {'policy': decl.name, 'atoms_used': used, 'combine': 'sum_totals_mod_vmod'}


def eval_factor(spec, atomvec_by_id, vmod):
    total = 0
    for aid in spec['atoms_used']:
        v = atomvec_by_id[aid]
        total = (total + (v if isinstance(v, int) else v[1])) % vmod
    return total


# Completeness: separators and attainability witnesses.

def build_completeness(histories, conts, policy_insts, gt_sig_of, reqs, classes, vmod):
    def atomvec(h):
        return tuple(atom_true_value(r, classes, h, vmod) for r in reqs)

    rep_of = {}
    for h in histories:
        av = atomvec(h)
        rep_of.setdefault(av, h)
    values = list(rep_of.keys())

    witnesses = {}
    for i, r in enumerate(reqs):
        aid = atom_id_of(r)
        for h in histories:
            av = atomvec(h)[i]
            neutral = (av == 0) if isinstance(av, int) else (av[1] == 0)
            if not neutral:
                witnesses[aid] = {'history': list(h), 'value': av}
                break

    pol_by_name = dict(policy_insts)
    cont_list = list(conts)
    separators = []
    # Every unordered pair gets a separator. checker.py rejects a partial list.
    pairs = itertools.combinations(range(len(values)), 2)
    for i, j in pairs:
        v1, v2 = values[i], values[j]
        h1, h2 = rep_of[v1], rep_of[v2]
        sig1, sig2 = gt_sig_of[h1], gt_sig_of[h2]
        # The sig layout is flat over (u in conts) x (policy in policy_insts).
        n_pol = len(policy_insts)
        found = None
        for k in range(len(sig1)):
            if sig1[k] != sig2[k]:
                u_idx, p_idx = divmod(k, n_pol)
                found = (cont_list[u_idx], policy_insts[p_idx][0], sig1[k], sig2[k])
                break
        if found is None:
            raise RuntimeError('completeness: no separator found for distinct atom-vectors '
                                '%r vs %r (h1=%r h2=%r), soundness/completeness mismatch' % (v1, v2, h1, h2))
        u, pname, out1, out2 = found
        separators.append({
            'h1': list(h1), 'h2': list(h2), 'v1': v1, 'v2': v2,
            'continuation': list(u), 'policy': pname, 'out1': out1, 'out2': out2,
        })
    return separators, witnesses, len(values)


# Per-instance certification. Every claim is self-checked on H_L before emission.

def needed_positions_for(req, classes, N):
    if req[0] == 'peer':
        return sorted(range(1, N + 1))
    cid = req[1] if req[0] == 'rev' else req[2]
    lo, hi = revclass_bounds(cid, classes)
    return [i for i in range(1, N + 1) if i >= lo and (hi is None or i <= hi)]


def certify_instance(name, pipeline, pipeline_id, decls, policy_insts, L, K, version_check=True,
                      extra_note=None):
    histories = C.all_histories(L)
    conts = C.continuations(K)
    classes = C.revision_classes(decls)
    reqs, field_req = C.derive_atom_requirements(pipeline, decls, L)

    if None in field_req:
        uncovered = [r for r in reqs if r[-1] is None]
        sup = C.position_support(pipeline, L)
        return {
            'instance': name, 'status': 'REFUSED',
            'refusal': {
                'obligation': 'atom-coverage',
                'reason': 'derive_atom_requirements found no field whose position-support '
                          'exactly covers a required attribution atom (pipeline erases the '
                          'needed positions irrecoverably). Soundness cannot be certified.',
                'pipeline_id': pipeline_id, 'peers': list(C.PEERS), 'vmod': C.VMOD, 'N': L,
                'uncovered_atoms': [
                    {'atom': atom_id_of(r), 'required_positions': needed_positions_for(r, classes, L)}
                    for r in uncovered
                ],
                'field_supports': {f: sorted(s) for f, s in sup.items()},
            },
        }

    status, retained, _trace = C.derive_retained_state(pipeline, frozenset(field_req), version_check=version_check)
    if status != 'OK':
        return {
            'instance': name, 'status': 'REFUSED',
            'refusal': {'obligation': 'field-resolution', 'reason': 'INFEASIBLE: %s' % (status,)},
        }

    evidence = soundness_evidence(pipeline, field_req, version_check, histories)
    evidence_by_field = {e['field']: e for e in evidence}

    # Self-check S1. Report the longest counterexample, since the first one
    # for a dropped field is usually the empty history and understates the loss.
    worst = None
    for h in sorted(histories, key=len, reverse=True):
        recon = evidence_reconstruct(evidence_by_field, pipeline, h)
        for r in reqs:
            got = atom_from_fields(r, recon)
            want = atom_true_value(r, classes, h, C.VMOD)
            if got != want:
                worst = (r, h, got, want)
                break
        if worst is not None:
            break
    if worst is not None:
        r, h, got, want = worst
        return {
            'instance': name, 'status': 'REFUSED',
            'refusal': {
                'obligation': 'soundness(atom-reconstruction)',
                'atom': atom_id_of(r), 'history': list(h),
                'reconstructed': got, 'true_value': want,
                'reason': 'retained/recomputed field(s) do not reconstruct the true '
                          'attribution-atom value on this history. Erasure lost '
                          'information the fragment claim needs.',
            },
        }

    # Self-check S2: policy factorisation.
    factor_specs = [policy_factor_spec(d, reqs, classes) for d in decls]
    for h in histories:
        av = {atom_id_of(r): atom_true_value(r, classes, h, C.VMOD) for r in reqs}
        for d, spec in zip(decls, factor_specs):
            got = eval_factor(spec, av, C.VMOD)
            want = None
            for pname, pol in policy_insts:
                if pname == d.name:
                    want = pol(h)
                    break
            if want is None:
                continue
            if got != want:
                return {
                    'instance': name, 'status': 'REFUSED',
                    'refusal': {
                        'obligation': 'soundness(policy-factorisation)',
                        'policy': d.name, 'history': list(h),
                        'factored': got, 'true_value': want,
                    },
                }

    gt_sig_of = C.gt_classes(histories, policy_insts, conts)
    separators, witnesses, n_values = build_completeness(
        histories, conts, policy_insts, gt_sig_of, reqs, classes, C.VMOD)

    for r in reqs:
        aid = atom_id_of(r)
        if aid not in witnesses:
            return {
                'instance': name, 'status': 'REFUSED',
                'refusal': {'obligation': 'completeness(attainability)', 'atom': aid,
                            'reason': 'no history in H_L realises a non-neutral value on this atom.'},
            }

    cert = {
        'instance': name,
        'status': 'CERTIFIED',
        'params': {'L': L, 'K': K, 'peers': list(C.PEERS), 'vmod': C.VMOD, 'version_check': version_check,
                   'pipeline_id': pipeline_id},
        'revision_classes': classes,
        'atoms': [{'id': atom_id_of(r), 'req': list(r[:-1]) + [r[-1]], 'field': r[-1]} for r in reqs],
        'soundness': {'stage_evidence': evidence, 'policy_factorisation': factor_specs},
        'completeness': {
            'n_distinct_atom_vectors': n_values,
            'n_pairs_certified': len(separators),
            'n_pairs_required': (n_values * (n_values - 1)) // 2,
            'separators': separators,
            'attainability_witnesses': witnesses,
        },
    }
    if extra_note:
        cert['note'] = extra_note
    return cert


def certify_refusal_out_of_fragment(name, pipeline, decls_in_fragment, policy_insts_ext, L, K):
    """first_peer_wins has a history-dependent filter, so it cannot be a PolicyDecl.
    Refuse at the declaration and give a pair that the Pi_hist atom-vector fails to separate."""
    histories = C.all_histories(L)
    conts = C.continuations(K)
    classes = C.revision_classes(decls_in_fragment)
    reqs, field_req = C.derive_atom_requirements(pipeline, decls_in_fragment, L)
    status, retained, _trace = C.derive_retained_state(pipeline, frozenset(field_req), version_check=True)
    state_fn = C.candidate_state_fn_atoms(pipeline, retained, reqs)
    gt_ext = C.gt_classes(histories, policy_insts_ext, conts)
    sound, complete, witness = C.check_sound_complete(histories, state_fn, gt_ext)
    out = {
        'instance': name,
        'status': 'REFUSED',
        'refusal': {
            'obligation': 'declaration(fold_M-of-fixed-filter)',
            'reason': "first_peer_wins reads seq[0]'s peer before filtering. Its "
                      "selection predicate is a function of the whole history, not a "
                      "fixed phi(peer,revision). It cannot be written as a PolicyDecl, "
                      "so no atom set can be derived for it.",
        },
    }
    if witness is not None:
        h1, h2 = witness
        out['witness'] = {
            'h1': list(h1), 'h2': list(h2),
            'note': "Pi_hist's own certified atom-vector is equal on h1,h2 (sound+complete "
                    "for Pi_hist) but first_peer_wins separates them under some continuation. "
                    "The fragment's construction cannot represent this policy.",
        }
    return out


class _with_universe:
    """Temporarily replace congruence's module-level universe (PEERS/ALPHABET/ALL_S).
    Its derivation code reads them as globals, so this runs it unmodified on a new peer set."""

    def __init__(self, peers):
        self.peers = tuple(peers)

    def __enter__(self):
        self._old = (C.PEERS, C.ALPHABET, C.ALL_S)
        C.PEERS = self.peers
        C.ALPHABET = tuple(itertools.product(self.peers, range(C.VMOD)))
        C.ALL_S = C.subsets(self.peers)
        return self

    def __exit__(self, *a):
        C.PEERS, C.ALPHABET, C.ALL_S = self._old
        return False


def main():
    t0 = time.time()
    os.makedirs(OUT_DIR, exist_ok=True)
    results = []

    def emit(cert):
        results.append(cert)
        path = os.path.join(OUT_DIR, cert['instance'].replace('/', '_') + '.json')
        with open(path, 'w') as f:
            json.dump(cert, f, indent=1, default=list)
        n_obl = 0
        if cert['status'] == 'CERTIFIED':
            n_obl = (len(cert['soundness']['stage_evidence']) * 2 * (2 ** 0)
                     + len(cert['soundness']['policy_factorisation'])
                     + cert['completeness']['n_pairs_certified']
                     + len(cert['completeness']['attainability_witnesses']))
        print('%-28s %-9s obligations~%-6d -> %s' % (cert['instance'], cert['status'], n_obl, path))
        return cert

    decls_base = C.pi_base_decls()
    decls_hist = C.pi_hist_decls()
    pi_base_pol = C.pi_base_instances()
    pi_hist_pol = C.pi_base_instances() + C.pi_hist_fixed_instances()

    emit(certify_instance('P1_Pi_base_L3', C.STAGES_AIF, 'P1_add', decls_base, pi_base_pol,
                           L=C.L_MAIN, K=C.K_MAIN))
    cert_hist_l3 = emit(certify_instance('P1_Pi_hist_L3', C.STAGES_AIF, 'P1_add', decls_hist, pi_hist_pol,
                                          L=C.L_MAIN, K=C.K_MAIN))
    assert cert_hist_l3['status'] == 'CERTIFIED', 'P1/Pi_hist L=3 must be certifiable'
    assert cert_hist_l3['completeness']['n_distinct_atom_vectors'] == 79, \
        'P1/Pi_hist L=3 must have exactly 79 attainable atom-vector classes'
    assert cert_hist_l3['completeness']['n_pairs_certified'] == cert_hist_l3['completeness']['n_pairs_required']

    emit(certify_instance('P1_Pi_base_L4', C.STAGES_AIF, 'P1_add', decls_base, pi_base_pol,
                           L=4, K=C.K_MAIN))

    # Expected to REFUSE. P1 splits on position parity, so at N=4 stream b carries
    # positions {2,4} and no field's support is exactly the class-2 singleton {2}.
    emit(certify_instance('P1_Pi_hist_L4', C.STAGES_AIF, 'P1_add', decls_hist, pi_hist_pol,
                           L=4, K=C.K_MAIN))

    emit(certify_instance('P2_Pi_base_L3', C.STAGES_LAYOUT, 'P2', decls_base, pi_base_pol,
                           L=C.L_MAIN, K=C.K_MAIN))

    # Mutants. Both must REFUSE.
    emit(certify_instance('P1prime_overwrite_Pi_base_L3', C.STAGES_AIF_OVERWRITE, 'P1_overwrite', decls_base, pi_base_pol,
                           L=C.L_MAIN, K=C.K_MAIN))
    emit(certify_instance('P1_Pi_hist_L3_vcOFF', C.STAGES_AIF, 'P1_add', decls_hist, pi_hist_pol,
                           L=C.L_MAIN, K=C.K_MAIN, version_check=False))

    # Out-of-fragment policy. Must REFUSE at the declaration obligation.
    pi_ext = pi_hist_pol + [('first_peer_wins', C.pol_first_peer_wins)]
    emit(certify_refusal_out_of_fragment('Pi_ext_first_peer_wins_L3', C.STAGES_AIF, decls_hist, pi_ext,
                                          L=C.L_MAIN, K=C.K_MAIN))

    # New universe with a third peer.
    with _with_universe(('A', 'B', 'C')):
        decls_base3 = C.pi_base_decls()
        pi_base_pol3 = C.pi_base_instances()
        cert3 = certify_instance('P1_ThreePeer_Pi_base_L2', C.STAGES_AIF, 'P1_add', decls_base3, pi_base_pol3,
                                  L=2, K=1,
                                  extra_note='new instance: PEERS extended to (A,B,C); same pipeline '
                                             'shape, unmodified congruence.py derivation code.')
    emit(cert3)

    # Three revision thresholds.
    decls_hist3 = C.pi_base_decls() + [
        C.PolicyDecl('after_1', None, C.RevisionFilter(1)),
        C.PolicyDecl('after_2', None, C.RevisionFilter(2)),
        C.PolicyDecl('after_3', None, C.RevisionFilter(3)),
    ]
    pi_hist3_pol = C.pi_base_instances() + [
        ('after_1', lambda seq: C.pol_after_r(seq, 1)),
        ('after_2', lambda seq: C.pol_after_r(seq, 2)),
        ('after_3', lambda seq: C.pol_after_r(seq, 3)),
    ]
    emit(certify_instance('P1_Pi_hist3_L3', C.STAGES_AIF, 'P1_add', decls_hist3, pi_hist3_pol,
                           L=C.L_MAIN, K=C.K_MAIN,
                           extra_note='3 revision thresholds instead of 2 (after_1/2/3).'))

    elapsed = time.time() - t0
    print('\nTotal certify.py runtime: %.2fs' % elapsed)

    with open(os.path.join(OUT_DIR, '_index.json'), 'w') as f:
        json.dump([{'instance': c['instance'], 'status': c['status']} for c in results], f, indent=1)

    n_refused = sum(1 for c in results if c['status'] == 'REFUSED')
    n_certified = sum(1 for c in results if c['status'] == 'CERTIFIED')
    print('%d certified, %d refused, %d total instances' % (n_certified, n_refused, len(results)))
    return results


if __name__ == '__main__':
    main()
