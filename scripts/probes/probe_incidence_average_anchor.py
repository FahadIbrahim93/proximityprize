"""Candidate production average-anchor ledger.
Author: Mikhail Izhutkin (@mashingaan)
No claim of a kernel-checked floor.
"""
import json
from fractions import Fraction

n=2**30
k=2**29
budget=n
count=budget+1
t=190185817
h=3*t-(n-k)
mass=count*t
overlap_slack=mass**2-(count**2*(h-1)*n+n*mass)
assert overlap_slack>0
assert 3*t-h+k==n
assert 0<h<=t<=n
assert t<budget
p=n*(2**128+192)+1
assert budget*2**128<=p
print(json.dumps(dict(n=n,k=k,budget=budget,witness_count=count,
    error_support_bound=t,required_pair_overlap=h,
    coverage_lemma_slack=overlap_slack,root_bound_slack=n-k-(3*t-h),
    covered_witness_slack=budget-t,
    candidate_floor=str(Fraction(t+1,n)),
    improvement_steps=t+1-178956972,
    existing_lemma='ArkLib.Coverage.exists_pair_inter_gt',
    evidence='exact numerical feasibility, pending incidence Lean bridge'),indent=2))
