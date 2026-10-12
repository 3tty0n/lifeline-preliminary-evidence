#!/usr/bin/env python3
"""Derive the coarsest policy congruence for a small transducer IR from its
declarations, and check it against brute-force ground truth.
Stdlib only. See README.md for scope."""

import itertools
import time

# ----------------------------------------------------------------------
# Universe
# ----------------------------------------------------------------------
PEERS = ('A', 'B')
VMOD = 3            # V = {0, 1, 2} under addition mod VMOD
L_MAIN = 3           # max history length (bounded universe) for the main check
K_MAIN = 2           # max continuation length
BOUNDARY_LS = (1, 2, 3, 4, 5, 6)   # history lengths probed for the boundary observation
BOUNDARY_K = 1                      # shallower continuations for the boundary loop, for speed

ALPHABET = tuple(itertools.product(PEERS, range(VMOD)))  # event = (peer, value)


def all_histories(L):
    out = []
    for n in range(L + 1):
        out.extend(itertools.product(ALPHABET, repeat=n))
    return out


def subsets(xs):
    xs = list(xs)
    out = []
    for n in range(len(xs) + 1):
        out.extend(itertools.combinations(xs, n))
    return [frozenset(s) for s in out]


ALL_S = subsets(PEERS)  # peer-set removals delta_S

# ----------------------------------------------------------------------
# Policies (ground-truth oracle). The revision of an event is its
# 1-indexed position in the sequence. That is what makes after_r observable.
# ----------------------------------------------------------------------

def pol_retain(seq):
    return sum(v for _, v in seq) % VMOD


def pol_revoke(seq, S):
    return sum(v for p, v in seq if p not in S) % VMOD


def pol_after_r(seq, r):
    return sum(v for i, (_, v) in enumerate(seq, 1) if i <= r) % VMOD


def pol_a_head_sum(seq):
    """Observes exactly what acc_a0 encodes, the peer sum of stream A's
    first event. It mirrors agg's own computation so that "no event" and
    "event of value 0" are conflated the same way acc_a0 conflates them."""
    ev_a, _ev_b = split_stream(seq)
    head = ev_a[:1]
    m = {p: 0 for p in PEERS}
    for p, v, _rev in head:
        m[p] = (m[p] + v) % VMOD
    return tuple(sorted(m.items()))


def pi_base_instances():
    insts = [('retain', lambda seq: pol_retain(seq))]
    for S in ALL_S:
        insts.append(('revoke(%s)' % (sorted(S),), lambda seq, S=S: pol_revoke(seq, S)))
    return insts


def pi_hist_fixed_instances():
    """Fixed and independent of L, so the boundary table varies L only."""
    return [('after_1', lambda seq: pol_after_r(seq, 1)),
            ('after_2', lambda seq: pol_after_r(seq, 2))]


def pi_snapshot_instances():
    return [('a_head_sum', pol_a_head_sum)]


def continuations(K):
    out = []
    for n in range(K + 1):
        out.extend(itertools.product(ALPHABET, repeat=n))
    return out


def gt_classes(histories, policy_insts, conts):
    """Return dict: history -> signature (its =_Pi class id)."""
    sig_of = {}
    for h in histories:
        sig = []
        for u in conts:
            hu = h + u
            for _, pol in policy_insts:
                sig.append(pol(hu))
        sig_of[h] = tuple(sig)
    return sig_of


def index_of(sig_of):
    return len(set(sig_of.values()))


def check_sound_complete(histories, state_fn, gt_sig_of):
    """Returns (sound, complete, witness). Soundness is checked first, so
    the witness is for the more serious failure."""
    state_to_gt = {}
    for h in histories:
        st = state_fn(h)
        gt = gt_sig_of[h]
        if st in state_to_gt:
            if state_to_gt[st][0] != gt:
                return False, None, (state_to_gt[st][1], h)
        else:
            state_to_gt[st] = (gt, h)

    gt_to_state = {}
    for h in histories:
        gt = gt_sig_of[h]
        st = state_fn(h)
        if gt in gt_to_state:
            if gt_to_state[gt][0] != st:
                return True, False, (gt_to_state[gt][1], h)
        else:
            gt_to_state[gt] = (st, h)

    return True, True, None


def naive_provenance_partition(histories):
    """Baseline for the provenance comparison. Per-peer sums over the whole history."""
    def prov(h):
        m = {p: 0 for p in PEERS}
        for p, v in h:
            m[p] = (m[p] + v) % VMOD
        return tuple((p, m[p]) for p in PEERS)
    return {h: prov(h) for h in histories}


# ----------------------------------------------------------------------
# Declarative transducer rules + THE single interpreter
# ----------------------------------------------------------------------

class Rule:
    """A declarative transducer rule.

    The IR is single-assignment, so a field name is already a versioned
    field (acc_a0 and acc_a are two versions of one accumulator).
    reads is enforced at run time by _ReadOnly. erases is only consumed
    by derive_retained_state. run() never deletes anything.
    recipe maps an erased field to None (unrecoverable) or to
    (other_fields, fn) where fn rebuilds it from those fields.
    """

    def __init__(self, name, reads, writes, erases, recipe, step):
        self.name = name
        self.reads = list(reads)
        self.writes = list(writes)
        self.erases = list(erases)
        self.recipe = dict(recipe)
        self.step = step


class _ReadOnly:
    """Raises if a step reads a field outside its declared reads."""

    def __init__(self, state, allowed, stage_name):
        self._state = state
        self._allowed = set(allowed)
        self._name = stage_name

    def __getitem__(self, k):
        if k not in self._allowed:
            raise RuntimeError(
                "Rule %r step touched field %r not declared in reads=%s"
                % (self._name, k, sorted(self._allowed)))
        return self._state[k]


def run(pipeline, history):
    """The single interpreter. Returns the reference trace with every field
    retained. Every candidate summary is a projection of this trace."""
    state = {}
    for stage in pipeline:
        view = _ReadOnly(state, stage.reads, stage.name)
        out = stage.step(view, history)
        if set(out) != set(stage.writes):
            raise RuntimeError(
                "Rule %r produced fields %s but declared writes=%s"
                % (stage.name, sorted(out), sorted(stage.writes)))
        state.update(out)
    return state


def derive_retained_state(pipeline, policy_fields, version_check=True):
    """The composition algorithm. Returns (status, retained_fields, trace).

    A worklist, not one backward sweep over stages. A recipe can need a
    field that a later stage erases (acc_a0 needs acc_a, which fuse
    erases), so every introduced field is rechecked against the global
    erasure map.
    """
    erased_by = {}
    for st in pipeline:
        for d in st.erases:
            erased_by[d] = st
    all_writable = set()
    for st in pipeline:
        all_writable |= set(st.writes)

    retained = set()
    seen = set()
    trace = []
    worklist = list(policy_fields)
    while worklist:
        d = worklist.pop(0)
        if d in seen:
            continue
        seen.add(d)
        st = erased_by.get(d)
        if st is None:
            retained.add(d)
            trace.append("  require %-9s never erased                                        -> RETAIN %s (trivial)" % (d, d))
            continue
        recipe = st.recipe.get(d)
        if version_check and recipe is not None:
            other_fields, _fn = recipe
            trace.append(
                "  require %-9s erased by %-40s recipe=needs%-20s vc=ON  -> RECOMPUTE (no retention)"
                % (d, st.name, str(other_fields)))
            worklist.extend(other_fields)
        elif version_check and recipe is None:
            retained.add(d)
            trace.append(
                "  require %-9s erased by %-40s recipe=None                    vc=ON  -> RETAIN %s explicitly"
                % (d, st.name, d))
        else:
            trace.append(
                "  require %-9s erased by %-40s recipe=%-9s          vc=OFF -> DROP (version check disabled)"
                % (d, st.name, "n/a" if recipe is None else "present-but-ignored"))

    truly_missing = {d for d in seen if d not in all_writable}
    if truly_missing:
        trace.append("  require %s -> never produced by any stage -> INFEASIBLE" % sorted(truly_missing))
        return ('INFEASIBLE', sorted(truly_missing)), None, trace

    return 'OK', frozenset(retained), trace


def verify_recipe(pipeline, stage, erased_field, histories):
    """Checks a recipe against run() on every history. Returns (ok, counterexample)."""
    recipe = stage.recipe.get(erased_field)
    if recipe is None:
        return None, None
    other_fields, fn = recipe
    for h in histories:
        ref = run(pipeline, h)
        got = fn({f: ref[f] for f in other_fields})
        if got != ref[erased_field]:
            return False, (h, got, ref[erased_field])
    return True, None


def candidate_state_fn(pipeline, retained_fields):
    fields = sorted(retained_fields)

    def state(h):
        ref = run(pipeline, h)
        return tuple(ref[f] for f in fields)
    return state


# ----------------------------------------------------------------------
# Pipeline 1: split -> agg -> inplace -> fuse.
# inplace overwrites acc_a0. In add mode acc_a0 = acc_a - tail_sum, so it
# has a recipe. In overwrite mode it is unrecoverable.
# ----------------------------------------------------------------------

def split_stream(h):
    """Splits h by position parity into (peer, value, revision) triples."""
    ev_a, ev_b = [], []
    for i, (p, v) in enumerate(h):
        rev = i + 1
        (ev_a if i % 2 == 0 else ev_b).append((p, v, rev))
    return tuple(ev_a), tuple(ev_b)


def peer_sum(events):
    m = {p: 0 for p in PEERS}
    for p, v, _rev in events:
        m[p] = (m[p] + v) % VMOD
    return tuple(sorted(m.items()))


def peer_sum_dict(events):
    return dict(peer_sum(events))


def _split_step(_view, h):
    ev_a, ev_b = split_stream(h)
    return {'events_a_head': ev_a[:1], 'events_a_tail': ev_a[1:], 'events_b': ev_b}


RULE_SPLIT = Rule(
    name='split', reads=[], writes=['events_a_head', 'events_a_tail', 'events_b'],
    erases=[], recipe={}, step=_split_step,
)

RULE_AGG = Rule(
    name='agg',
    reads=['events_a_head', 'events_b'],
    writes=['acc_a0', 'acc_b'],
    erases=['events_a_head', 'events_b'],
    # A per-peer sum loses event identity and position.
    recipe={'events_a_head': None, 'events_b': None},
    step=lambda view, h: {
        'acc_a0': peer_sum(view['events_a_head']),
        'acc_b': peer_sum(view['events_b']),
    },
)


def _recover_acc_a0(vals):
    acc_a = dict(vals['acc_a'])
    tail_sum = dict(vals['tail_sum'])
    return tuple(sorted((p, (acc_a[p] - tail_sum[p]) % VMOD) for p in PEERS))


def _inplace_step(mode):
    def step(view, _h):
        acc_a0 = dict(view['acc_a0'])
        tail = view['events_a_tail']
        tail_sum = peer_sum_dict(tail)
        acc = dict(acc_a0)
        for p, v, _rev in tail:
            if mode == 'add':
                acc[p] = (acc[p] + v) % VMOD
            else:  # overwrite, the bad local rule
                acc[p] = v
        return {'acc_a': tuple(sorted(acc.items())), 'tail_sum': tuple(sorted(tail_sum.items()))}
    return step


RULE_INPLACE_ADD = Rule(
    name='inplace[cell += v]',
    reads=['acc_a0', 'events_a_tail'],
    writes=['acc_a', 'tail_sum'],
    erases=['acc_a0', 'events_a_tail'],
    recipe={'acc_a0': (('acc_a', 'tail_sum'), _recover_acc_a0), 'events_a_tail': None},
    step=_inplace_step('add'),
)

RULE_INPLACE_OVERWRITE = Rule(
    name='inplace[cell = v]  [BAD LOCAL RULE, unsafe]',
    reads=['acc_a0', 'events_a_tail'],
    writes=['acc_a', 'tail_sum'],
    erases=['acc_a0', 'events_a_tail'],
    # Overwrite keeps only the last event per peer, so acc_a0 is lost.
    # Same shape as the add rule, opposite recipe.
    recipe={'acc_a0': None, 'events_a_tail': None},
    step=_inplace_step('overwrite'),
)

RULE_FUSE = Rule(
    name='fuse',
    reads=['acc_a', 'acc_b'],
    writes=['final'],
    erases=['acc_a', 'acc_b'],
    recipe={'acc_a': None, 'acc_b': None},
    step=lambda view, h: {
        'final': tuple((p, (dict(view['acc_a'])[p] + dict(view['acc_b'])[p]) % VMOD) for p in PEERS)
    },
)

STAGES_AIF = [RULE_SPLIT, RULE_AGG, RULE_INPLACE_ADD, RULE_FUSE]
STAGES_AIF_OVERWRITE = [RULE_SPLIT, RULE_AGG, RULE_INPLACE_OVERWRITE, RULE_FUSE]


# ----------------------------------------------------------------------
# Pipeline 2: source -> layout -> agg.
# ----------------------------------------------------------------------

RULE_SOURCE_EVENTS = Rule(
    name='source', reads=[], writes=['events'], erases=[], recipe={},
    step=lambda _view, h: {'events': h},
)

RULE_LAYOUT = Rule(
    name='layout',
    reads=['events'],
    writes=['packed'],
    erases=['events'],
    # Packing drops revision, and nothing else carries it.
    recipe={'events': None},
    step=lambda view, h: {'packed': tuple((p, v) for p, v in view['events'])},
)

RULE_AGG_FINAL = Rule(
    name='agg(final)',
    reads=['packed'],
    writes=['final'],
    erases=['packed'],
    recipe={'packed': None},
    step=lambda view, h: {'final': peer_sum(tuple((p, v, 0) for p, v in view['packed']))},
)

STAGES_LAYOUT = [RULE_SOURCE_EVENTS, RULE_LAYOUT, RULE_AGG_FINAL]


# ----------------------------------------------------------------------
# Value-level refinement, kept separate from derive_retained_state and run().
# ----------------------------------------------------------------------

def zero_neutral_canon(value):
    """Anonymises the peer of 0-valued events in a raw-event field. No sum
    policy can see who sent a 0. The event itself stays, because its
    position still shifts later after_r continuations."""
    if isinstance(value, tuple) and value and isinstance(value[0], tuple) and len(value[0]) == 3:
        return tuple((None if v == 0 else p, v, rev) for (p, v, rev) in value)
    return value


def candidate_state_fn_refined(pipeline, retained_fields):
    base = candidate_state_fn(pipeline, retained_fields)

    def state(h):
        return tuple(zero_neutral_canon(v) for v in base(h))
    return state


# ----------------------------------------------------------------------
# Declaration-driven congruence.
#
# Each policy is pi = fold_M . filter_phi with M = (Z/VMOD, +, 0). phi is
# declared structurally (PeerFilter, RevisionFilter), so the atoms a policy
# needs can be derived rather than hand-listed. revision_classes() reads the
# atoms off the declared thresholds. position_support() finds which fields
# carry each atom by running the real Rule steps on symbolic values. The
# resulting field set goes to derive_retained_state() unchanged.
# ----------------------------------------------------------------------

class PeerFilter:
    """phi(e) = e.peer not in exclude."""
    def __init__(self, exclude):
        self.exclude = frozenset(exclude)


class RevisionFilter:
    """phi(e) = e.revision <= max_rev."""
    def __init__(self, max_rev):
        self.max_rev = max_rev


class PolicyDecl:
    """Either filter may be None. Both set means a joint (peer, revision) filter."""
    def __init__(self, name, peer_filter, rev_filter):
        self.name = name
        self.peer_filter = peer_filter
        self.rev_filter = rev_filter


def pi_base_decls():
    decls = [PolicyDecl('retain', PeerFilter(frozenset()), None)]
    for S in ALL_S:
        decls.append(PolicyDecl('revoke(%s)' % (sorted(S),), PeerFilter(S), None))
    return decls


def pi_hist_decls():
    return pi_base_decls() + [
        PolicyDecl('after_1', None, RevisionFilter(1)),
        PolicyDecl('after_2', None, RevisionFilter(2)),
    ]


def pi_snapshot_decls():
    return [PolicyDecl('a_head_sum', PeerFilter(frozenset()), RevisionFilter(1))]


def revision_classes(decls):
    """Thresholds {1,2} give classes {1}, {2}, '>2'. No threshold gives one 'ALL' class."""
    thresholds = sorted({d.rev_filter.max_rev for d in decls if d.rev_filter is not None})
    if not thresholds:
        return [('ALL', 1, None)]
    classes, lo = [], 1
    for t in thresholds:
        classes.append((t, lo, t))
        lo = t + 1
    classes.append(('>%d' % thresholds[-1], lo, None))
    return classes


def revclass_of(rev, classes):
    for cid, lo, hi in classes:
        if rev >= lo and (hi is None or rev <= hi):
            return cid
    return classes[-1][0]


class AtomVec:
    """A formal Z-linear combination of position atoms. % is a no-op
    because the modulus does not change which atoms are present. This lets
    unmodified Rule.step code run on symbolic values."""
    __slots__ = ('coef',)

    def __init__(self, coef=None):
        self.coef = dict(coef) if coef else {}

    @staticmethod
    def unit(pos):
        return AtomVec({pos: 1})

    def __add__(self, other):
        if not isinstance(other, AtomVec):
            if other == 0:
                return AtomVec(self.coef)
            raise TypeError(other)
        out = dict(self.coef)
        for k, v in other.coef.items():
            out[k] = out.get(k, 0) + v
        return AtomVec(out)
    __radd__ = __add__

    def __sub__(self, other):
        out = dict(self.coef)
        for k, v in other.coef.items():
            out[k] = out.get(k, 0) - v
        return AtomVec(out)

    def __mod__(self, m):
        return self

    def support(self):
        return frozenset(k for k, v in self.coef.items() if v != 0)

    def __repr__(self):
        return 'AtomVec(%s)' % dict(self.coef)


def _atomvec_support(val):
    found = set()

    def walk(x):
        if isinstance(x, AtomVec):
            found.update(x.support())
        elif isinstance(x, tuple):
            for e in x:
                walk(e)
    walk(val)
    return frozenset(found)


def position_support(pipeline, N, peer='A'):
    """Returns {field: positions its value depends on}, found by running the
    pipeline on a symbolic history of N one-hot atoms."""
    h = tuple((peer, AtomVec.unit(i)) for i in range(1, N + 1))
    ref = run(pipeline, h)
    return {field: _atomvec_support(val) for field, val in ref.items()}


def covering_field(pipeline, sup, needed_positions, prefer='earliest'):
    """Picks a field whose support is exactly needed_positions. 'earliest'
    keeps presence information that after_r needs. 'latest' picks the most
    aggregated field, which routes through recipes."""
    cands = [f for f, s in sup.items() if s == needed_positions]
    if not cands:
        return None
    field_stage_idx = {}
    for i, st in enumerate(pipeline):
        for f in st.writes:
            field_stage_idx.setdefault(f, i)
    key = (lambda f: field_stage_idx.get(f, 10 ** 9)) if prefer == 'earliest' \
        else (lambda f: -field_stage_idx.get(f, -1))
    return min(cands, key=key)


def derive_atom_requirements(pipeline, decls, N, prefer='earliest'):
    """Derives each policy's atoms from its filters. Peer-only filters need
    per-peer marginals. Revision-only filters need per-class marginals.
    Joint filters need a joint atom, since the side condition shows joint
    atoms are not in the marginal span. retain is covered by revoke(empty).
    Returns (reqs, field_req). field_req contains None when no field
    covers an atom, which is how the overwrite mutant is caught."""
    classes = revision_classes(decls)
    sup = position_support(pipeline, N)
    reqs, field_req, seen = [], set(), set()

    def rev_classes_upto(r):
        return [c for c in classes if c[2] is not None and c[2] <= r]

    for d in decls:
        if d.peer_filter is not None and d.rev_filter is None:
            for p in PEERS:
                if p in d.peer_filter.exclude:
                    continue
                key = ('peer', p)
                if key in seen:
                    continue
                seen.add(key)
                full_range = frozenset(range(1, N + 1))
                f = covering_field(pipeline, sup, full_range, prefer)
                reqs.append(('peer', p, f))
                field_req.add(f)
        elif d.rev_filter is not None and d.peer_filter is None:
            for cid, lo, hi in rev_classes_upto(d.rev_filter.max_rev):
                key = ('rev', cid)
                if key in seen:
                    continue
                seen.add(key)
                positions = frozenset(i for i in range(1, N + 1) if revclass_of(i, classes) == cid)
                f = covering_field(pipeline, sup, positions, prefer)
                reqs.append(('rev', cid, f))
                field_req.add(f)
        elif d.peer_filter is not None and d.rev_filter is not None:
            for p in PEERS:
                if p in d.peer_filter.exclude:
                    continue
                for cid, lo, hi in rev_classes_upto(d.rev_filter.max_rev):
                    key = ('joint', p, cid)
                    if key in seen:
                        continue
                    seen.add(key)
                    positions = frozenset(i for i in range(1, N + 1) if revclass_of(i, classes) == cid)
                    f = covering_field(pipeline, sup, positions, prefer)
                    reqs.append(('joint', p, cid, f))
                    field_req.add(f)
    return reqs, field_req


_MISSING = ()  # value of a dropped field when version_check=False


def candidate_state_fn_atoms(pipeline, retained_fields, reqs, version_check=True):
    """Reads each required atom back out of the retained state.

    With version_check on, every required field is retained or rebuilt by
    a verified recipe, so reading ref[f] is safe. With it off nothing is
    recomputed, so a field not literally retained reads as _MISSING.
    rev and joint atoms also carry a presence count. Whether a position is
    occupied shifts every later revision, and after_r sees that.
    """
    fields_needed = {r[-1] for r in reqs}

    def state(h):
        ref = run(pipeline, h)
        if version_check:
            proj = {f: ref[f] for f in fields_needed}
        else:
            proj = {f: (ref[f] if f in retained_fields else _MISSING) for f in fields_needed}
        out = []
        for r in reqs:
            kind, f = r[0], r[-1]
            val = proj[f]
            if kind == 'peer':
                _, p, _f = r
                total = sum(item[1] for item in val if item[0] == p) % VMOD
                out.append(total)
            elif kind == 'rev':
                total = 0
                for item in val:
                    total = (total + item[1]) % VMOD
                out.append((len(val), total))
            else:  # joint
                _, p, cid, _f = r
                items = [it for it in val if it[0] == p]
                total = sum(it[1] for it in items) % VMOD
                out.append((len(items), total))
        return tuple(out)
    return state


# ---- Side condition, checked over GF(VMOD) ----

def _gf_rref(rows, p):
    """Row-reduces over GF(p). Returns (rref, rank)."""
    rows = [list(r) for r in rows]
    ncols = len(rows[0]) if rows else 0
    rank = 0
    for col in range(ncols):
        pivot = next((r for r in range(rank, len(rows)) if rows[r][col] % p != 0), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][col], p - 2, p)
        rows[rank] = [(x * inv) % p for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col] % p != 0:
                f = rows[r][col]
                rows[r] = [(rows[r][i] - f * rows[rank][i]) % p for i in range(ncols)]
        rank += 1
    return rows, rank


def _gf_in_span(rows, vec, p):
    _, r1 = _gf_rref(rows, p)
    _, r2 = _gf_rref(rows + [list(vec)], p)
    return r1 == r2


def side_condition_report(p_lines):
    """A retained atom is recoverable iff its indicator over the joint
    (peer x revision-class) space lies in the GF(VMOD) span of Pi_hist's
    filter indicators. Subtraction is allowed because M is a group."""
    revclasses = [1, 2, '>2']
    atoms = [(pe, rc) for pe in PEERS for rc in revclasses]
    idx = {a: i for i, a in enumerate(atoms)}

    def indicator(peer_ok, rev_ok):
        v = [0] * len(atoms)
        for (pe, rc) in atoms:
            if peer_ok(pe) and rev_ok(rc):
                v[idx[(pe, rc)]] = 1
        return v

    rows = [indicator(lambda pe: True, lambda rc: True)]  # retain
    for S in ALL_S:
        rows.append(indicator(lambda pe, S=S: pe not in S, lambda rc: True))  # revoke(S)
    rows.append(indicator(lambda pe: True, lambda rc: rc == 1))        # after_1
    rows.append(indicator(lambda pe: True, lambda rc: rc in (1, 2)))   # after_2

    _, rank = _gf_rref(rows, VMOD)
    marginal_atoms = {
        'peerA': indicator(lambda pe: pe == 'A', lambda rc: True),
        'peerB': indicator(lambda pe: pe == 'B', lambda rc: True),
        'rev1': indicator(lambda pe: True, lambda rc: rc == 1),
        'rev2': indicator(lambda pe: True, lambda rc: rc == 2),
    }
    joint_A1 = [0] * len(atoms)
    joint_A1[idx[('A', 1)]] = 1

    p_lines("Side condition: a retained atom is recoverable iff its indicator")
    p_lines("lies in the GF(%d)-linear span of Pi_hist's declared filters, over" % VMOD)
    p_lines("the full joint (peer x revision-class) attribution space (%d atoms)." % len(atoms))
    p_lines("rank(span(Pi_hist's %d declared filters)) = %d / %d joint atoms" % (len(rows), rank, len(atoms)))
    all_marginal_in_span = True
    for name, v in marginal_atoms.items():
        ok = _gf_in_span(rows, v, VMOD)
        all_marginal_in_span &= ok
        p_lines("  %-6s in span? %s" % (name, ok))
    joint_ok = _gf_in_span(rows, joint_A1, VMOD)
    p_lines("  joint atom (A,1) [peer AND revision together] in span? %s" % joint_ok)
    p_lines("Conclusion: the %d MARGINAL atoms this derivation actually retains" % len(marginal_atoms))
    p_lines("(peerA, peerB, rev1, rev2) are each individually selectable from Pi_hist's")
    p_lines("declared filters (side condition holds for them: rank %d = %d needed)."
            % (rank, len(marginal_atoms)))
    p_lines("The FINER joint atom (A,1) is NOT: Pi_hist never combines a peer restriction")
    p_lines("and a revision restriction in the SAME filter, so its span cannot reach a")
    p_lines("cell that needs both at once. This is why derive_atom_requirements")
    p_lines("uses marginal, not joint, atoms for peer-only/revision-only policies, and")
    p_lines("falls back to a JOINT atom only for a policy (a_head_sum) that")
    p_lines("itself declares both filters together.")
    return all_marginal_in_span and not joint_ok


def pol_first_peer_wins(seq):
    """Out of fragment. The filter depends on seq[0], so no fixed phi expresses it."""
    if not seq:
        return 0
    first_peer = seq[0][0]
    return sum(v for p, v in seq if p == first_peer) % VMOD


# ----------------------------------------------------------------------
# Report helpers
# ----------------------------------------------------------------------

def print_dag(p, stages, title):
    p(title)
    for st in stages:
        recipe_desc = {f: ('needs%s' % (r[0],) if r is not None else 'None')
                        for f, r in st.recipe.items()}
        p("    %-40s reads=%-40s writes=%-16s erases=%s"
          % (st.name, str(st.reads), str(st.writes), str(st.erases)))
        if recipe_desc:
            p("        recipe: %s" % recipe_desc)
    p("")


def report_pipeline(p, label, histories, gt_sig_of, state_fn, expect_sound=True, expect_complete=True):
    sound, complete, witness = check_sound_complete(histories, state_fn, gt_sig_of)
    p("  %-46s sound=%-5s complete=%s" % (label, sound, complete))
    if witness is not None:
        h1, h2 = witness
        p("      witness pair: h1=%s  h2=%s" % (h1, h2))
        p("      candidate state(h1)=%s  state(h2)=%s" % (state_fn(h1), state_fn(h2)))
    return sound, complete, witness


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------

def main():
    t0 = time.time()
    lines = []

    def p(s=''):
        print(s)
        lines.append(s)

    histories = all_histories(L_MAIN)
    conts = continuations(K_MAIN)
    pi_base = pi_base_instances()
    pi_hist = pi_base_instances() + pi_hist_fixed_instances()
    # Pi_snapshot is tested alone. Adding Pi_base would make an overwrite
    # witness ambiguous between a broken fold and a wrong recipe decision.
    pi_snap = pi_snapshot_instances()

    gt_base = gt_classes(histories, pi_base, conts)
    gt_hist = gt_classes(histories, pi_hist, conts)
    # Pi_snapshot uses K=0, not K_MAIN. a_head_sum observes a snapshot frozen
    # at h, whereas gt_classes re-evaluates on h+u. Lifting this restriction
    # requires a per-field "observed at" stage in gt_classes.
    gt_snap = gt_classes(histories, pi_snap, continuations(0))
    gt_base_index = index_of(gt_base)
    gt_hist_index = index_of(gt_hist)

    p("=== Dataflow DAGs (test set): reads/writes/erases/recipe are the ONLY")
    p("    thing run() and derive_retained_state() consume ===")
    print_dag(p, STAGES_AIF, "Pipeline P1: split -> agg -> inplace(add) -> fuse")
    print_dag(p, STAGES_AIF_OVERWRITE, "Pipeline P1': split -> agg -> inplace(OVERWRITE) -> fuse  [bad local rule]")
    print_dag(p, STAGES_LAYOUT, "Pipeline P2: source -> layout -> agg")

    p("=== Declaration-driven exact coarsest congruence ===")
    p("Ground truth index, Pi_base (retain+revoke(S)): %d classes" % gt_base_index)
    p("Ground truth index, Pi_hist (Pi_base + after_1,after_2): %d classes" % gt_hist_index)
    p("")

    results = {}
    N = L_MAIN

    decls_base = pi_base_decls()
    reqs_base, field_req_base = derive_atom_requirements(STAGES_AIF, decls_base, N)
    status, retained, _trace = derive_retained_state(STAGES_AIF, frozenset(field_req_base), version_check=True)
    p("[P1 / Pi_base / version_check=ON]  DERIVED field requirement = %s" % (sorted(field_req_base),))
    p("  -> retained fields = %s" % (sorted(retained) if status == 'OK' else status,))
    state_fn = candidate_state_fn_atoms(STAGES_AIF, retained, reqs_base)
    results['P1_base'] = report_pipeline(p, "P1, add mode, vc=ON", histories, gt_base, state_fn)
    idx = len(set(state_fn(h) for h in histories))
    p("  index = %d  (target: exactly %d)" % (idx, gt_base_index))
    p("")

    decls_hist = pi_hist_decls()
    reqs_hist, field_req_hist = derive_atom_requirements(STAGES_AIF, decls_hist, N)
    status, retained, _trace = derive_retained_state(STAGES_AIF, frozenset(field_req_hist), version_check=True)
    p("[P1 / Pi_hist / version_check=ON]  DERIVED field requirement = %s" % (sorted(field_req_hist),))
    p("  -> retained fields = %s" % (sorted(retained) if status == 'OK' else status,))
    state_fn = candidate_state_fn_atoms(STAGES_AIF, retained, reqs_hist)
    results['P1_hist'] = report_pipeline(p, "P1, add mode, vc=ON", histories, gt_hist, state_fn)
    candidate_hist_index = len(set(state_fn(h) for h in histories))
    p("  index = %d  (target: exactly %d)" % (candidate_hist_index, gt_hist_index))
    p("")

    status, retained, trace_off = derive_retained_state(STAGES_AIF, frozenset(field_req_hist), version_check=False)
    p("[P1 / Pi_hist / version_check=OFF, version check disabled] retained fields = %s"
      % (sorted(retained) if status == 'OK' else status,))
    state_fn = candidate_state_fn_atoms(STAGES_AIF, retained, reqs_hist, version_check=False)
    results['P1_hist_vcoff'] = report_pipeline(p, "P1, vc=OFF (version check disabled)", histories, gt_hist, state_fn)
    p("")

    reqs_base_ow, field_req_base_ow = derive_atom_requirements(STAGES_AIF_OVERWRITE, decls_base, N)
    if None in field_req_base_ow:
        p("[P1' / Pi_base / overwrite local rule]  derive_atom_requirements finds NO field")
        p("  covers position 1's contribution any more (overwrite discards the pre-fold")
        p("  accumulator instead of adding into it) -> INFEASIBLE. This follows from the")
        p("  declarations, before any history is compared.")
        results['P1_overwrite'] = (False, None, None)
    else:
        status, retained, _trace = derive_retained_state(STAGES_AIF_OVERWRITE, frozenset(field_req_base_ow), version_check=True)
        state_fn_overwrite = candidate_state_fn_atoms(STAGES_AIF_OVERWRITE, retained, reqs_base_ow)
        p("[P1' / Pi_base / overwrite local rule]  retained fields = %s (bad VALUES)" % (sorted(retained),))
        results['P1_overwrite'] = report_pipeline(p, "P1', overwrite inplace", histories, gt_base, state_fn_overwrite)
    p("")

    reqs_base_p2, field_req_base_p2 = derive_atom_requirements(STAGES_LAYOUT, decls_base, N)
    status, retained, _trace = derive_retained_state(STAGES_LAYOUT, frozenset(field_req_base_p2), version_check=True)
    p("[P2 / Pi_base / version_check=ON]  DERIVED field requirement = %s" % (sorted(field_req_base_p2),))
    p("  -> retained fields = %s" % (sorted(retained) if status == 'OK' else status,))
    state_fn_layout = candidate_state_fn_atoms(STAGES_LAYOUT, retained, reqs_base_p2)
    results['P2_base'] = report_pipeline(p, "P2 layout->agg, vc=ON", histories, gt_base, state_fn_layout)
    p("")

    sound, complete, witness = results['P1_hist_vcoff']
    if not sound and witness is not None:
        h1, h2 = witness
        p("=== Concrete mutant pair (version check disabled loses derived atom info) ===")
        p("  h1 = %s" % (h1,))
        p("  h2 = %s" % (h2,))
        for name, pol in pi_hist:
            v1, v2 = pol(h1), pol(h2)
            if v1 != v2:
                p("  distinguishing policy: %-10s pol(h1)=%d != pol(h2)=%d" % (name, v1, v2))
        p("")

    p("=== Recipe and version-check branch (Pi_snapshot, a JOINT atom) ===")
    p("a_head_sum declares BOTH a peer_filter and a rev_filter, so it needs a joint")
    p("(peer=A, revision<=1) atom. The side condition holds for a Pi with ONE such policy.")
    p("Using prefer='latest' (the most-AGGREGATED covering field, acc_a0) instead of")
    p("the default 'earliest' routes this atom through inplace's erasure,")
    p("so the recipe/version-check machinery gets exercised:")
    p("")
    decls_snap = pi_snapshot_decls()
    for mode_name, pipeline in (('ADD (recipe present)', STAGES_AIF),
                                 ('OVERWRITE (no recipe)', STAGES_AIF_OVERWRITE)):
        reqs_snap, field_req_snap = derive_atom_requirements(pipeline, decls_snap, N, prefer='latest')
        p("  inplace mode: %s   DERIVED field requirement = %s" % (mode_name, sorted(field_req_snap)))
        status, retained, trace = derive_retained_state(pipeline, frozenset(field_req_snap), version_check=True)
        for line in trace:
            p(line)
        p("  -> derived retained fields = %s" % (sorted(retained) if status == 'OK' else status,))
        state_fn = candidate_state_fn_atoms(pipeline, retained, reqs_snap)
        sound, complete, witness = report_pipeline(p, "  Pi_snapshot, vc=ON (%s)" % mode_name, histories, gt_snap, state_fn)
        p("")

    ok, bad = verify_recipe(STAGES_AIF, RULE_INPLACE_ADD, 'acc_a0', histories)
    p("  recipe callable check (acc_a0 = acc_a - tail_sum, add mode): %s over all %d histories"
      % ("PASS" if ok else "FAIL: %s" % (bad,), len(histories)))
    p("")

    # With the version check off, acc_a0 is dropped even without a recipe.
    reqs_snap_ow, field_req_snap_ow = derive_atom_requirements(STAGES_AIF_OVERWRITE, decls_snap, N, prefer='latest')
    status, retained, trace_snap_off = derive_retained_state(STAGES_AIF_OVERWRITE, frozenset(field_req_snap_ow), version_check=False)
    p("  inplace mode: OVERWRITE, version_check=OFF (drop despite no recipe)")
    for line in trace_snap_off:
        p(line)
    p("  -> derived retained fields = %s" % (sorted(retained) if status == 'OK' else status,))
    state_fn = candidate_state_fn_atoms(STAGES_AIF_OVERWRITE, retained, reqs_snap_ow, version_check=False)
    results['Pi_snapshot_vcoff'] = report_pipeline(p, "  Pi_snapshot, vc=OFF", histories, gt_snap, state_fn)
    p("")

    status, retained, trace_infeasible = derive_retained_state(STAGES_AIF, frozenset({'no_such_field'}), version_check=True)
    p("  INFEASIBLE branch demo: requiring a field no stage ever writes ->")
    for line in trace_infeasible:
        p(line)
    p("")


    prov = naive_provenance_partition(histories)
    prov_index = len(set(prov.values()))
    status, retained, _trace = derive_retained_state(STAGES_AIF, frozenset(field_req_base), version_check=True)
    state_fn = candidate_state_fn_atoms(STAGES_AIF, retained, reqs_base)
    correct_index = len(set(state_fn(h) for h in histories))
    same_partition = all(
        (prov[h1] == prov[h2]) == (state_fn(h1) == state_fn(h2))
        for h1, h2 in itertools.islice(itertools.product(histories, histories), 0, 200000)
    )
    p("=== Does the P1/Pi_base derived candidate coincide with provenance projection? ===")
    p("provenance-projection index: %d classes    derived-candidate index: %d classes" % (prov_index, correct_index))
    p("Coincide on this universe? %s" % ("YES" if same_partition and prov_index == correct_index == gt_base_index else "NO"))
    p("(The candidate is derived from local transducer rules. It is not claimed to be smaller than provenance projection.)")
    p("")

    p("=== Side condition for exactness, checked over GF(%d) ===" % VMOD)
    side_ok = side_condition_report(p)
    p("")

    p("=== A policy OUTSIDE the fragment: 'first contribution wins' ===")
    p("first_peer_wins(seq): observes only whichever peer sent the chronologically")
    p("FIRST event. Its filter depends on the HISTORY ITSELF, not on a fixed")
    p("attribution predicate. Not expressible as fold_M(filter_phi) for a fixed phi.")
    pi_ext = pi_hist + [('first_peer_wins', pol_first_peer_wins)]
    gt_ext = gt_classes(histories, pi_ext, conts)
    gt_ext_index = index_of(gt_ext)
    p("Ground truth index, Pi_hist u {first_peer_wins}: %d classes (vs %d for Pi_hist alone)"
      % (gt_ext_index, gt_hist_index))
    status, retained, _trace = derive_retained_state(STAGES_AIF, frozenset(field_req_hist), version_check=True)
    state_fn_frag = candidate_state_fn_atoms(STAGES_AIF, retained, reqs_hist)
    sound_ext, complete_ext, witness_ext = check_sound_complete(histories, state_fn_frag, gt_ext)
    p("Pi_hist's OWN exact atom-vector, reused against Pi_ext (unchanged, NOT re-derived):")
    p("  sound=%s  complete=%s" % (sound_ext, complete_ext))
    if witness_ext is not None:
        h1, h2 = witness_ext
        p("  witness pair: h1=%s  h2=%s" % (h1, h2))
        p("  (equal atom-vector, but first_peer_wins can tell them apart via SOME")
        p("   continuation u. A fold over a fixed filter cannot represent")
        p("   'whichever peer went first'.)")
    p("This is the fragment boundary. It is a policy shape the construction cannot")
    p("represent, shown by an unsoundness witness.")
    p("")

    p("=== Boundary observation: Pi FIXED across L ===")
    p("Pi_hist = {after_1, after_2} u Pi_base, the same policy set for every L")
    p("%-4s %-26s %-26s" % ("L", "index(Pi_base)", "index(Pi_hist, FIXED)"))
    boundary_rows = []
    pi_hist_fixed = pi_base_instances() + pi_hist_fixed_instances()
    bconts = continuations(BOUNDARY_K)
    for L in BOUNDARY_LS:
        hs = all_histories(L)
        idx_base = index_of(gt_classes(hs, pi_base, bconts))
        idx_hist = index_of(gt_classes(hs, pi_hist_fixed, bconts))
        boundary_rows.append((L, idx_base, idx_hist))
        p("%-4d %-26d %-26d" % (L, idx_base, idx_hist))
    p("(continuation depth K=%d for this loop, vs K=%d for the main check above, for speed)" % (BOUNDARY_K, K_MAIN))
    p("")
    growing = any(boundary_rows[i][2] < boundary_rows[i + 1][2] for i in range(len(boundary_rows) - 1))
    base_plateaus = boundary_rows[-1][1] == boundary_rows[-2][1]
    hist_plateau_L = next((row[0] for row in boundary_rows
                            if row == boundary_rows[-1] or
                            all(r[2] == row[2] for r in boundary_rows[boundary_rows.index(row):])), None)
    base_plateau_L = next(row[0] for row in boundary_rows
                           if all(r[1] == row[1] for r in boundary_rows[boundary_rows.index(row):]))
    p("With Pi fixed, both indices are bounded. Pi_base plateaus at %d (reached by L=%d)."
      % (boundary_rows[-1][1], base_plateau_L))
    p("Pi_hist plateaus at %d (reached only by L=%d). The difference comes only from"
      % (boundary_rows[-1][2], hist_plateau_L))
    p("the two history-sensitive policies.")

    elapsed = time.time() - t0
    p("")
    p("Runtime: %.2fs" % elapsed)

    assert results['P1_base'][0] and results['P1_base'][1], "P1/Pi_base must be sound+complete"
    assert results['P1_base'][0] is True and len(set(candidate_state_fn_atoms(STAGES_AIF,
        derive_retained_state(STAGES_AIF, frozenset(field_req_base), version_check=True)[1],
        reqs_base)(h) for h in histories)) == gt_base_index == 9, "Pi_base must be EXACTLY 9 classes"
    assert results['P1_hist'][0] and results['P1_hist'][1], "P1/Pi_hist (vc=ON) must be sound AND complete"
    assert candidate_hist_index == gt_hist_index == 79, "P1/Pi_hist must be EXACTLY 79 classes"
    assert not results['P1_hist_vcoff'][0], "P1/Pi_hist vc=OFF was expected to be UNSOUND"
    assert not results['P1_overwrite'][0], "P1' overwrite local rule was expected to be UNSOUND (or structurally INFEASIBLE)"
    assert results['P2_base'][0] and results['P2_base'][1], "P2 (layout) /Pi_base must be sound+complete"
    assert not results['Pi_snapshot_vcoff'][0], "Pi_snapshot vc=OFF (overwrite, no recipe) was expected to be UNSOUND"
    assert ok, "acc_a0 recipe must check out against the reference trace"
    assert base_plateaus, "Pi_base index expected to plateau across L"
    assert growing, "Pi_hist index expected to grow with L even though Pi is fixed"
    assert side_ok, "side condition: marginal atoms in span, joint atom NOT in span, as reported"
    assert not sound_ext, "Pi_hist's exact atom-vector must be UNSOUND once first_peer_wins is added (fragment boundary)"
    assert gt_ext_index > gt_hist_index, "adding first_peer_wins must grow the ground-truth index"
    assert elapsed < 60, "must run in under 60s"

    return "\n".join(lines)


if __name__ == "__main__":
    main()
