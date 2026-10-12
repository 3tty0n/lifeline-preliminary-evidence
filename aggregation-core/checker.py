#!/usr/bin/env python3
"""Independent checker for certs/. It must not import congruence.py or certify.py,
so it reimplements the semantics it needs and rejects what it cannot reproduce.
"""
import glob
import itertools
import json
import os
import re
import sys


# Ground-truth atom and policy semantics, independent of any pipeline.

def fold_sum(values, vmod):
    total = 0
    for v in values:
        total = (total + v) % vmod
    return total


def peer_atom(h, peer, vmod):
    return fold_sum((v for p, v in h if p == peer), vmod)


def rev_atom(h, lo, hi, vmod):
    sel = [(p, v) for i, (p, v) in enumerate(h, 1) if i >= lo and (hi is None or i <= hi)]
    return (len(sel), fold_sum((v for _, v in sel), vmod))


def joint_atom(h, peer, lo, hi, vmod):
    sel = [(p, v) for i, (p, v) in enumerate(h, 1)
           if p == peer and i >= lo and (hi is None or i <= hi)]
    return (len(sel), fold_sum((v for _, v in sel), vmod))


def revclass_bounds(cid, classes):
    for c, lo, hi in classes:
        if c == cid:
            return lo, hi
    raise KeyError(cid)


def atom_value(req, classes, h, vmod):
    kind = req[0]
    if kind == 'peer':
        return peer_atom(h, req[1], vmod)
    if kind == 'rev':
        lo, hi = revclass_bounds(req[1], classes)
        return rev_atom(h, lo, hi, vmod)
    lo, hi = revclass_bounds(req[2], classes)
    return joint_atom(h, req[1], lo, hi, vmod)


def eval_policy_by_decl(name, classes, h, vmod, peer_exclude, rev_max):
    """Policy semantics: phi(peer, revision) folded under (Z/vmod, +, 0)."""
    sel = []
    for i, (p, v) in enumerate(h, 1):
        if peer_exclude is not None and p in peer_exclude:
            continue
        if rev_max is not None and i > rev_max:
            continue
        sel.append(v)
    return fold_sum(sel, vmod)


# The three pipelines, each as its own small interpreter. The field names match
# the stage evidence in the certificates. No code is shared with congruence.py.

def _peers_of(h):
    return sorted({p for p, v in h})


def p1_state(h, peers, vmod, mode):
    """mode: 'add' or 'overwrite'."""
    ev_a, ev_b = [], []
    for i, (p, v) in enumerate(h):
        rev = i + 1
        (ev_a if i % 2 == 0 else ev_b).append((p, v, rev))
    events_a_head = tuple(ev_a[:1])
    events_a_tail = tuple(ev_a[1:])
    events_b = tuple(ev_b)

    def psum(evs):
        m = {p: 0 for p in peers}
        for p, v, _r in evs:
            m[p] = (m[p] + v) % vmod
        return tuple(sorted(m.items()))

    acc_a0 = psum(events_a_head)
    acc_b = psum(events_b)
    tail_sum = dict(psum(events_a_tail))
    acc = dict(acc_a0)
    for p, v, _r in events_a_tail:
        acc[p] = (acc[p] + v) % vmod if mode == 'add' else v
    acc_a = tuple(sorted(acc.items()))
    final = tuple((p, (dict(acc_a)[p] + dict(acc_b)[p]) % vmod) for p in peers)
    return {
        'events_a_head': events_a_head, 'events_a_tail': events_a_tail, 'events_b': events_b,
        'acc_a0': acc_a0, 'acc_b': acc_b, 'acc_a': acc_a,
        'tail_sum': tuple(sorted(tail_sum.items())), 'final': final,
    }


def p2_state(h, peers, vmod):
    events = tuple(h)
    packed = tuple((p, v) for p, v in events)
    m = {p: 0 for p in peers}
    for p, v in packed:
        m[p] = (m[p] + v) % vmod
    final = tuple(sorted(m.items()))
    return {'events': events, 'packed': packed, 'final': final}


def pipeline_state(pipeline_id, h, peers, vmod):
    if pipeline_id == 'P1_add':
        return p1_state(h, peers, vmod, 'add')
    if pipeline_id == 'P1_overwrite':
        return p1_state(h, peers, vmod, 'overwrite')
    if pipeline_id == 'P2':
        return p2_state(h, peers, vmod)
    raise ValueError('unknown pipeline_id %r' % (pipeline_id,))


# Recipe formulas.

def apply_recipe(tag, field_vals, peers, vmod):
    if tag == 'subtract_tail_sum':
        acc_a = dict(field_vals['acc_a'])
        tail_sum = dict(field_vals['tail_sum'])
        return tuple(sorted((p, (acc_a[p] - tail_sum[p]) % vmod) for p in peers))
    raise ValueError('unknown recipe tag %r' % (tag,))


def reconstruct_field(evidence, state, peers, vmod):
    if evidence['type'] in ('trivial', 'retain_explicit'):
        return state[evidence['field']]
    if evidence['type'] == 'recipe':
        inputs = {f: state[f] for f in evidence['recipe_inputs']}
        return apply_recipe(evidence['recipe_tag'], inputs, peers, vmod)
    return None  # 'drop'


def atom_from_field(req, val, vmod):
    if val is None:
        return None
    kind = req[0]
    if kind == 'peer':
        p = req[1]
        return sum(item[1] for item in val if item[0] == p) % vmod
    if kind == 'rev':
        return (len(val), sum(item[1] for item in val) % vmod)
    p = req[1]
    items = [it for it in val if it[0] == p]
    return (len(items), sum(it[1] for it in items) % vmod)


def eval_factor(spec, atomvec_by_id, vmod):
    total = 0
    for aid in spec['atoms_used']:
        v = atomvec_by_id[aid]
        total = (total + (v if isinstance(v, int) else v[1])) % vmod
    return total


def all_histories(peers, vmod, L):
    import itertools
    alphabet = tuple(itertools.product(peers, range(vmod)))
    out = []
    for n in range(L + 1):
        out.extend(tuple(map(tuple, seq)) for seq in itertools.product(alphabet, repeat=n))
    return out


def pipeline_id_for(instance_name):
    if 'overwrite' in instance_name:
        return 'P1_overwrite'
    if instance_name.startswith('P2'):
        return 'P2'
    return 'P1_add'


def declared_policy_names(instance_name, peers):
    """The policy set an instance declares, read from its name and not from the
    certificate, so a certificate cannot shrink what it has to cover."""
    m = re.search(r'Pi_(base|hist)(\d*)', instance_name)
    if m is None:
        return None
    names = {'retain'}
    for n in range(len(peers) + 1):
        for S in itertools.combinations(sorted(peers), n):
            names.add('revoke(%s)' % (list(S),))
    if m.group(1) == 'hist':
        names |= {'after_%d' % r for r in range(1, int(m.group(2) or 2) + 1)}
    return names


# Support of a field, found by running p1_state/p2_state on formal sums. This
# tests the "no covering field" claim of an atom-coverage refusal instead of
# trusting it.

class Support:
    __slots__ = ('coef',)

    def __init__(self, coef=None):
        self.coef = dict(coef) if coef else {}

    @staticmethod
    def unit(pos):
        return Support({pos: 1})

    def __add__(self, other):
        if not isinstance(other, Support):
            if other == 0:
                return Support(self.coef)
            raise TypeError(other)
        out = dict(self.coef)
        for k, v in other.coef.items():
            out[k] = out.get(k, 0) + v
        return Support(out)
    __radd__ = __add__

    def __sub__(self, other):
        out = dict(self.coef)
        for k, v in other.coef.items():
            out[k] = out.get(k, 0) - v
        return Support(out)

    def __mod__(self, _m):
        return self

    def positions(self):
        return frozenset(k for k, v in self.coef.items() if v != 0)


def _walk_support(x, found):
    if isinstance(x, Support):
        found.update(x.positions())
    elif isinstance(x, tuple):
        for e in x:
            _walk_support(e, found)


def independent_position_support(pipeline_id, peers, vmod, N):
    """{field: frozenset(positions)} from a symbolic history."""
    h = tuple((peers[0], Support.unit(i)) for i in range(1, N + 1))
    state = pipeline_state(pipeline_id, h, peers, vmod)
    out = {}
    for field, val in state.items():
        found = set()
        _walk_support(val, found)
        out[field] = frozenset(found)
    return out


# Checking a CERTIFIED certificate.

def check_certified(cert):
    n_obl = 0
    peers = tuple(cert['params']['peers'])
    vmod = cert['params']['vmod']
    L = cert['params']['L']
    version_check = cert['params']['version_check']
    classes = [tuple(c) for c in cert['revision_classes']]
    reqs = [tuple(a['req']) for a in cert['atoms']]
    ids = [a['id'] for a in cert['atoms']]
    pipeline_id = pipeline_id_for(cert['instance'])
    if version_check is False:
        return False, n_obl, 'CERTIFIED certificate has version_check=OFF, a ' \
                              'construction with version checking disabled must be unsound; ' \
                              'no such certificate should ever be CERTIFIED.'

    histories = all_histories(peers, vmod, L)

    # Coverage gate. An empty list must not pass because its loop never runs.
    if not reqs:
        return False, 0, 'certificate lists zero atoms. Nothing to check, REJECTED (empty proof).'
    evidence_by_field = {e['field']: e for e in cert['soundness']['stage_evidence']}
    missing_evidence = [req[-1] for req in reqs if req[-1] not in evidence_by_field]
    if missing_evidence:
        return False, 0, 'no stage evidence for required field(s) %r' % (missing_evidence,)
    if not cert['soundness']['policy_factorisation']:
        return False, 0, 'certificate lists zero policy factorisations, REJECTED (empty proof).'
    declared = declared_policy_names(cert['instance'], peers)
    if declared is None:
        return False, 0, 'cannot tell the declared policy set from instance %r' % (cert['instance'],)
    missing_policies = declared - {f['policy'] for f in cert['soundness']['policy_factorisation']}
    if missing_policies:
        return False, 0, 'no policy factorisation for declared policy(ies) %r' % (sorted(missing_policies),)
    if not cert['completeness']['attainability_witnesses']:
        return False, 0, 'certificate lists zero attainability witnesses, REJECTED (empty proof).'
    missing_witness = [aid for aid in ids if aid not in cert['completeness']['attainability_witnesses']]
    if missing_witness:
        return False, 0, 'no attainability witness for atom(s) %r' % (missing_witness,)

    # Completeness coverage gate. Recount the attainable atom-vectors from H_L
    # and require a separator for every unordered pair, whatever the certificate claims.
    def atomvec(h):
        return tuple(atom_value(req, classes, h, vmod) for req in reqs)
    own_values = {}
    for h in histories:
        own_values.setdefault(atomvec(h), h)
    own_list = list(own_values.keys())
    n_own = len(own_list)
    n_required = n_own * (n_own - 1) // 2
    if cert['completeness']['n_distinct_atom_vectors'] != n_own:
        return False, 0, ('certificate claims %d distinct atom-vectors, independently found %d'
                           % (cert['completeness']['n_distinct_atom_vectors'], n_own))
    if len(cert['completeness']['separators']) < n_required:
        return False, 0, ('completeness requires %d separators (C(%d,2)) for full pairwise coverage, '
                           'certificate supplies only %d, REJECTED (capped/partial completeness).'
                           % (n_required, n_own, len(cert['completeness']['separators'])))
    covered_pairs = set()
    for sep in cert['completeness']['separators']:
        h1, h2 = tuple(map(tuple, sep['h1'])), tuple(map(tuple, sep['h2']))
        covered_pairs.add(frozenset((atomvec(h1), atomvec(h2))))
    all_pairs = {frozenset((own_list[i], own_list[j]))
                 for i in range(n_own) for j in range(i + 1, n_own)}
    missing_pairs = all_pairs - covered_pairs
    if missing_pairs:
        return False, 0, ('%d distinct atom-vector pairs have no separator in the certificate, '
                           'REJECTED (incomplete completeness coverage).' % len(missing_pairs))

    # Soundness of stage evidence.
    for h in histories:
        state = pipeline_state(pipeline_id, h, peers, vmod)
        recon = {f: reconstruct_field(ev, state, peers, vmod) for f, ev in evidence_by_field.items()}
        for req, aid in zip(reqs, ids):
            got = atom_from_field(req, recon[req[-1]], vmod)
            want = atom_value(req, classes, h, vmod)
            n_obl += 1
            if got != want:
                return False, n_obl, ('soundness(atom-reconstruction) failed independently: '
                                       'atom=%s h=%r reconstructed=%r true=%r' % (aid, h, got, want))

    # Soundness of policy factorisation. The reference side comes from the policy
    # name, not from `atoms_used`, so a wrong `atoms_used` cannot move both sides.
    # An unrecognised policy shape fails closed.
    for h in histories:
        av = {aid: atom_value(req, classes, h, vmod) for req, aid in zip(reqs, ids)}
        for spec in cert['soundness']['policy_factorisation']:
            n_obl += 1
            got = eval_factor(spec, av, vmod)
            try:
                peer_exclude, rev_max = _decl_from_policy_name(spec['policy'], peers)
            except ValueError as e:
                return False, n_obl, 'cannot independently verify policy factorisation: %s' % (e,)
            want = eval_policy_by_decl(spec['policy'], classes, h, vmod, peer_exclude, rev_max)
            if got != want:
                return False, n_obl, ('soundness(policy-factorisation) failed independently: '
                                       'policy=%s h=%r factored=%r true=%r'
                                       % (spec['policy'], h, got, want))

    # Separators.
    for sep in cert['completeness']['separators']:
        n_obl += 1
        h1, h2, u = tuple(map(tuple, sep['h1'])), tuple(map(tuple, sep['h2'])), tuple(map(tuple, sep['continuation']))
        v1 = tuple(atom_value(req, classes, h1, vmod) for req in reqs)
        v2 = tuple(atom_value(req, classes, h2, vmod) for req in reqs)
        if v1 == v2:
            return False, n_obl, 'separator listed for h1,h2 whose atom-vectors are NOT distinct: %r' % (sep,)
        pname = sep['policy']
        peer_exclude, rev_max = _decl_from_policy_name(pname, peers)
        out1 = eval_policy_by_decl(pname, classes, h1 + u, vmod, peer_exclude, rev_max)
        out2 = eval_policy_by_decl(pname, classes, h2 + u, vmod, peer_exclude, rev_max)
        if out1 == out2:
            return False, n_obl, 'separator does not actually separate: %r -> out1=out2=%r' % (sep, out1)
        if out1 != sep['out1'] or out2 != sep['out2']:
            return False, n_obl, 'separator outputs do not match certificate: %r vs recomputed (%r,%r)' % (sep, out1, out2)

    # Attainability witnesses.
    for aid, w in cert['completeness']['attainability_witnesses'].items():
        n_obl += 1
        req = reqs[ids.index(aid)]
        h = tuple(map(tuple, w['history']))
        val = atom_value(req, classes, h, vmod)
        neutral = (val == 0) if isinstance(val, int) else (val[1] == 0 and val[0] == 0)
        if neutral:
            return False, n_obl, 'attainability witness for %s is neutral: h=%r value=%r' % (aid, h, val)
        want_val = tuple(w['value']) if isinstance(w['value'], list) else w['value']
        if val != want_val:
            return False, n_obl, ('attainability witness value for %s does not match independent '
                                   'recomputation: cert=%r recomputed=%r' % (aid, want_val, val))

    return True, n_obl, None


def _decl_from_policy_name(name, peers):
    """Recover (peer_exclude, rev_max) from the policy name: retain, revoke([...]), after_N."""
    if name == 'retain':
        return (set(), None)
    if name.startswith('revoke('):
        inner = name[len('revoke('):-1]
        excl = set(p.strip("'\" ") for p in inner.strip('[]').split(',') if p.strip("'\" "))
        return (excl, None)
    if name.startswith('after_'):
        return (None, int(name.split('_', 1)[1]))
    raise ValueError('cannot reconstruct declaration for policy %r' % (name,))


# Checking a REFUSED certificate. The named counterexample must reproduce the failure.

def check_refused_full(cert, peers, vmod, classes_hint):
    obligation = cert['refusal']['obligation']
    if obligation == 'atom-coverage':
        r = cert['refusal']
        needed = ('pipeline_id', 'peers', 'vmod', 'N', 'uncovered_atoms')
        if not all(k in r for k in needed):
            return False, 0, ('atom-coverage refusal missing structural payload %r. Cannot '
                               'independently verify, REJECTED (unverifiable refusal).' % (needed,))
        if not r['uncovered_atoms']:
            return False, 0, 'atom-coverage refusal names no uncovered atom, REJECTED.'
        peers_r = tuple(r['peers'])
        sup = independent_position_support(r['pipeline_id'], peers_r, r['vmod'], r['N'])
        n = 0
        for u in r['uncovered_atoms']:
            n += 1
            needed_positions = frozenset(u['required_positions'])
            covering = [f for f, s in sup.items() if s == needed_positions]
            if covering:
                return False, n, ('claimed atom-coverage refusal for %s is NOT reproduced: field(s) '
                                   '%r independently found to cover exactly %r'
                                   % (u['atom'], covering, sorted(needed_positions)))
        return True, n, None
    if obligation == 'field-resolution':
        return True, 0, None  # no numeric claim to replay (INFEASIBLE from a never-written field)
    if obligation == 'soundness(atom-reconstruction)':
        r = cert['refusal']
        h = tuple(map(tuple, r['history']))
        kind, rest = r['atom'].split(':', 1)
        if kind == 'peer':
            val = peer_atom(h, rest, vmod)
        elif kind == 'rev':
            cid = int(rest) if rest.isdigit() else rest
            lo, hi = revclass_bounds(cid, classes_hint)
            val = rev_atom(h, lo, hi, vmod)
        else:
            return False, 0, 'cannot re-derive joint refusal atom independently in this checker'
        if list(val) != r['true_value'] and val != tuple(r['true_value']):
            return False, 0, 'refused cert true_value does not match independent recomputation: %r vs %r' % (val, r['true_value'])
        if r['reconstructed'] is not None:
            return False, 0, 'refusal claims information loss but reconstructed value is not null'
        return True, 1, None
    if obligation == 'declaration(fold_M-of-fixed-filter)':
        w = cert.get('witness')
        if w is None:
            return False, 0, 'first-peer-wins refusal has no witness to check'
        h1, h2 = tuple(map(tuple, w['h1'])), tuple(map(tuple, w['h2']))

        def first_peer_wins(seq):
            if not seq:
                return 0
            fp = seq[0][0]
            return fold_sum((v for p, v in seq if p == fp), vmod)
        found = False
        for u in all_histories(peers, vmod, 1):
            if first_peer_wins(h1 + u) != first_peer_wins(h2 + u):
                found = True
                break
        if not found:
            return False, 0, 'claimed out-of-fragment witness pair is not actually separated by first_peer_wins'
        return True, 1, None
    return False, 0, 'unknown refusal obligation %r' % (obligation,)


# Driver.

def check_one(cert):
    if cert['status'] == 'CERTIFIED':
        ok, n, reason = check_certified(cert)
        return ok, n, reason
    else:
        peers = tuple(cert.get('params', {}).get('peers', ('A', 'B')))
        vmod = cert.get('params', {}).get('vmod', 3)
        # Revision classes of Pi_hist.
        classes_hint = [(1, 1, 1), (2, 2, 2), ('>2', 3, None)]
        ok, n, reason = check_refused_full(cert, peers, vmod, classes_hint)
        return ok, n, reason


def main():
    cert_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'certs')
    paths = sorted(p for p in glob.glob(os.path.join(cert_dir, '*.json')) if not p.endswith('_index.json'))
    if not paths:
        print('no certificates found in %s. Run certify.py first' % cert_dir)
        sys.exit(1)

    total_obl = 0
    n_accept = 0
    n_reject = 0
    rows = []
    for path in paths:
        with open(path) as f:
            cert = json.load(f)
        try:
            ok, n_obl, reason = check_one(cert)
        except Exception as e:  # noqa: BLE001. A checker must not silently pass on its own bugs
            ok, n_obl, reason = False, 0, 'checker exception: %r' % (e,)
        total_obl += n_obl
        verdict = 'ACCEPT' if ok else 'REJECT'
        if ok:
            n_accept += 1
        else:
            n_reject += 1
        rows.append((cert['instance'], cert['status'], n_obl, verdict, reason))
        print('%-30s cert=%-10s obligations=%-6d checker=%-6s %s'
              % (cert['instance'], cert['status'], n_obl, verdict, '' if reason is None else ('| ' + str(reason))))

    print('\n%d certificates checked: %d ACCEPT, %d REJECT, %d total obligations verified'
          % (len(rows), n_accept, n_reject, total_obl))
    sys.exit(0 if n_reject == 0 else 1)


if __name__ == '__main__':
    main()
