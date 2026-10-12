#!/usr/bin/env python3
"""Re-derive the leave numbers from the archived sources and run data.
Needs no GPU or PyPy build. Exits non-zero if any number differs from the proposal.
"""
import csv
import os
import statistics
import subprocess
import sys
import tarfile
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
TP = os.path.join(HERE, 'tensorpypy')
RUN = os.path.join(TP, 'benchmark/results/rtx3090/motion-2026-09-23')
sys.path.insert(0, os.path.join(TP, 'benchmark/motion'))
import count_lines as CL  # noqa: E402

FAILS = []


def expect(label, got, want):
    ok = got == want
    print('%-58s %-12s %s' % (label, got, 'ok' if ok else 'DIFFERS (want %s)' % (want,)))
    if not ok:
        FAILS.append(label)


def py(*args):
    return subprocess.run([sys.executable, '-I'] + list(args),
                          capture_output=True, text=True)


# The rule may use only motion_iface. The contaminated copy must fail.
print('== audit (benchmark/eval/audit_rules.py)')
audit = os.path.join(TP, 'benchmark/eval/audit_rules.py')
expect('rule_leave.py passes the audit',
       py(audit, os.path.join(TP, 'pypy/module/_metatensor/rule_leave.py')).returncode, 0)
expect('rule_leave_leaky.py is rejected',
       py(audit, os.path.join(TP, 'benchmark/motion/rule_leave_leaky.py')).returncode != 0, True)
expect('rule length (code lines, count_lines.py)',
       CL.count('pypy/module/_metatensor/rule_leave.py', 'all'), 7)

print('\n== line counts (benchmark/motion/count_lines.py, unchanged)')
CL.ROOT = TP
m_rows, n_rule = CL.side(CL.MOTION)
a_rows, n_adapter = CL.side(CL.ADAPTER)
expect('N_rule (everything on the MOTION side)', n_rule, 246)
expect('N_adapter (everything on the adapter side)', n_adapter, 47)


def counted(path, what):
    """The line numbers count_lines.count() counts, mirroring it."""
    src = open(os.path.join(TP, path)).read()
    tree = CL.ast.parse(src)
    lines = CL.code_lines(src) - CL.docstring_lines(tree)
    if what == 'all':
        return lines
    marks = src.splitlines()
    lines -= {i + 1 for i, l in enumerate(marks) if '# [harness]' in l}
    kind, arg = what
    if kind == 'marked':
        return lines & {i + 1 for i, l in enumerate(marks) if '# [%s]' % arg in l}
    inside = {n for a, b in CL.spans(tree, arg) for n in range(a, b + 1)}
    return lines & inside if kind == 'only' else lines - inside


roles = [r for r in csv.DictReader(
    (l for l in open(os.path.join(HERE, 'linecount_roles.tsv'))
     if not l.startswith('#')), delimiter='\t')]
for side, items in (('M', CL.MOTION), ('A', CL.ADAPTER)):
    want = {(p, n) for _, p, w in items for n in counted(p, w)}
    have = {(r['file'], int(r['line'])) for r in roles if r['side'] == side}
    expect('roles table covers exactly the counted lines (%s)' % side,
           have == want, True)
src = {}
bad = [r for r in roles if not src.setdefault(
    r['file'], open(os.path.join(TP, r['file'])).read().splitlines()
)[int(r['line']) - 1].strip().startswith(r['text'].strip())]
expect('roles table text matches the source lines', len(bad), 0)


def n(side, *role_set, sub=None):
    return sum(1 for r in roles if r['side'] == side and r['role'] in role_set
               and (sub is None or r['sub'] == sub))


expect('MOTION lines that exist only because of the change (D+E:D)',
       n('M', 'D', 'E:D'), 139)
expect('adapter lines that exist only because of the change (D)',
       n('A', 'D'), 27)
expect('hand-written lines that decide what to keep',
       n('M', 'D', sub='keep'), 21)

print('\n== checker (benchmark/motion/check_leave.py) on data.tar.gz')
check = os.path.join(TP, 'benchmark/motion/check_leave.py')
HIST = ['h1', 'h2', 'h3', 'h2post', 'none']
with tempfile.TemporaryDirectory() as tmp:
    with tarfile.open(os.path.join(RUN, 'data.tar.gz')) as t:
        t.extractall(tmp, filter='data')
    d = os.path.join(tmp, 'leave')
    ok = all(py(check, os.path.join(d, '%s_%s' % (impl, h))).returncode == 0
             for h in HIST for impl in ('ref', 'motion', 'adapter'))
    expect('ref, motion, adapter pass the checker on all 5 histories', ok, True)
    same = all(py(check, '--pair', os.path.join(d, 'ref_' + h),
                  os.path.join(d, '%s_%s' % (impl, h))).returncode == 0
               for h in HIST for impl in ('motion', 'adapter'))
    expect('motion and adapter equal the interpreter-only run', same, True)
    for mut in ('erase', 'late'):
        caught = [h for h in HIST
                  if py(check, os.path.join(d, '%s_%s' % (mut, h))).returncode]
        expect('mutant %s caught on' % mut, ','.join(caught), 'h2')
    leave = list(csv.DictReader(open(os.path.join(tmp, 'leave.tsv')), delimiter='\t'))
    perf = list(csv.DictReader(open(os.path.join(tmp, 'leave_perf.tsv')), delimiter='\t'))

print('\n== traces compiled by the meta-tracer (leave.tsv, archived run)')
expect('motion rows with loops > 0 and bridges > 0',
       sum(int(r['loops']) > 0 and int(r['bridges']) > 0
           for r in leave if r['impl'] == 'motion'), len(HIST))
expect('ref rows (jit off), loops and bridges',
       ','.join(sorted({'%s/%s' % (r['loops'], r['bridges'])
                        for r in leave if r['impl'] == 'ref'})), '0/0')
print('\n== launches per step (leave.tsv, leave_perf.tsv)')
for impl, want in (('motion', '1.160'), ('adapter', '5.000')):
    vals = {r['steady_launches'] for r in leave if r['impl'] == impl}
    expect('leave.tsv steady launches, %s (all histories)' % impl,
           ','.join(sorted(vals)), want)
binaries = {r['binary'] for r in leave + perf}
expect('binary of every row', ','.join(sorted(binaries)), 'a99ad86b05e2')


def med(cfg, sync, field):
    xs = [float(r[field]) for r in perf if r['config'] == cfg and r['sync'] == sync]
    return len(xs), round(statistics.median(xs), 2)


for cfg, want in (('retained', 1.16), ('unretained', 1.16), ('adapter', 5.0)):
    expect('leave_perf.tsv n=65536 sync=0 %s (runs, median)' % cfg,
           med(cfg, '0', 'steady_launches'), (10, want))
print('\nnot in the proposal, for reference (median step us, sync=1):',
      {c: med(c, '1', 'step_us')[1] for c in ('retained', 'unretained', 'adapter')},
      '\nmedian steady launches with sync=1:',
      {c: med(c, '1', 'steady_launches')[1] for c in ('retained', 'adapter')})

print('\n%s' % ('all leave numbers re-derived' if not FAILS
                else 'DIFFERS: ' + '; '.join(FAILS)))
sys.exit(1 if FAILS else 0)
