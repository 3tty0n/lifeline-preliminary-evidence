#!/usr/bin/env python3
"""Tampered certificates that checker.py must reject."""
import copy
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import checker as CK  # noqa: E402


def load(name):
    with open(os.path.join(HERE, 'certs', name + '.json')) as f:
        return json.load(f)


def empty_proof(c):
    c['atoms'] = []
    c['soundness']['stage_evidence'] = []
    c['soundness']['policy_factorisation'] = []
    c['completeness']['separators'] = []
    c['completeness']['attainability_witnesses'] = {}


def drop_last_witness(c):
    w = c['completeness']['attainability_witnesses']
    del w[sorted(w)[-1]]


CONTROLS = [
    ('empty proof', empty_proof),
    ('no separators', lambda c: c['completeness'].update(separators=[])),
    ('separators truncated to half',
     lambda c: c['completeness'].update(
         separators=c['completeness']['separators'][
             :len(c['completeness']['separators']) // 2])),
    ('one separator missing',
     lambda c: c['completeness'].update(
         separators=c['completeness']['separators'][:-1])),
    ('one attainability witness missing', drop_last_witness),
    ('no stage evidence',
     lambda c: c['soundness'].update(stage_evidence=[])),
    ('no policy factorisation',
     lambda c: c['soundness'].update(policy_factorisation=[])),
    ('one policy factorisation entry missing',
     lambda c: c['soundness'].update(
         policy_factorisation=c['soundness']['policy_factorisation'][:-1])),
]


def empty_refusal(c):
    c['refusal']['uncovered_atoms'] = []


REFUSAL_CONTROLS = [
    ('P1_Pi_hist_L4', 'REFUSED with no uncovered atom', empty_refusal),
]


def main():
    bad = 0
    for inst in ('P1_Pi_hist_L3', 'P1_Pi_base_L3'):
        base = load(inst)
        ok, _ = CK.check_one(base)[:2]
        print('%-14s %-40s checker=%s (must be ACCEPT)'
              % (inst, 'untampered', 'ACCEPT' if ok else 'REJECT'))
        bad += not ok
        for label, tamper in CONTROLS:
            c = copy.deepcopy(base)
            tamper(c)
            ok = CK.check_one(c)[0]
            print('%-14s %-40s checker=%s' % (inst, label,
                                               'ACCEPT  <-- FAIL' if ok
                                               else 'REJECT'))
            bad += ok
    for inst, label, tamper in REFUSAL_CONTROLS:
        c = copy.deepcopy(load(inst))
        tamper(c)
        ok = CK.check_one(c)[0]
        print('%-14s %-40s checker=%s' % (inst, label,
                                           'ACCEPT  <-- FAIL' if ok
                                           else 'REJECT'))
        bad += ok
    print('negative controls: %s' % ('all rejected' if not bad
                                      else '%d FAILED' % bad))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
