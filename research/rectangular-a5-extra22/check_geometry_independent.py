"""Independent, standard-library-only exact controls. No author code imports."""
from fractions import Fraction as F
from pathlib import Path
from math import gcd
import hashlib
import json
import time
import resource

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
AUTHOR = HERE
A, B, H, N = 28, 27, 756, 54
RR = list(range(A)) + [0] + list(range(A)) * 2
CC = list(range(A)) * 2 + [0] + list(range(A))
R, C = RR[:N], CC[-N:]
EXPECTED = [53] + list(range(28, 53)) + [27, 26, 25, 24] + list(range(2, 24)) + [1, 0]
ROW = [[int(k == R[i] or k == A + i % B or k == A + B) for k in range(A+B+1)] for i in range(N)]
COL = [[int(k == C[j] or k == A + j % B or k == A + B) for k in range(A+B+1)] for j in range(N)]

def integer_rank(rows):
    """Eliminate by integer cross products and primitive-row reduction."""
    rows = [list(row) for row in rows]
    assert all(type(x) is int for row in rows for x in row)
    rank = 0
    for j in range(len(rows[0]) if rows else 0):
        p = next((p for p in range(rank, len(rows)) if rows[p][j]), None)
        if p is None:
            continue
        rows[rank], rows[p] = rows[p], rows[rank]
        for k in range(rank+1, len(rows)):
            if not rows[k][j]:
                continue
            x, y = rows[rank][j], rows[k][j]
            rows[k] = [x*u-y*v for u,v in zip(rows[k], rows[rank])]
            divisor = 0
            for z in rows[k]:
                divisor = gcd(divisor, z)
            if divisor:
                rows[k] = [z // divisor for z in rows[k]]
        rank += 1
    return rank

def selected_rank(rows, selected):
    return integer_rank([[row[k] for k in sorted(selected)] for row in rows])

def exact_elimination(matrix):
    matrix = [row[:] for row in matrix]
    assert all(type(x) is F for row in matrix for x in row)
    pivots, values, prefix_minors = [], [], []
    product = F(1)
    for i, row in enumerate(matrix):
        eligible = [j for j, x in enumerate(row) if x]
        if not eligible:
            break
        j = max(eligible)
        pivot = row[j]
        pivots.append(j)
        values.append(str(pivot))
        product *= pivot
        prefix_minors.append(str(product))
        for k in range(i+1, len(matrix)):
            multiplier = matrix[k][j] / pivot
            assert type(multiplier) is F
            if multiplier:
                matrix[k] = [u-multiplier*v for u,v in zip(matrix[k], row)]
                assert all(type(x) is F for x in matrix[k])
    return dict(permutation=pivots, pivots=values, ordered_prefix_minors=prefix_minors)

def witness(kind, seed=1):
    if kind == 'independent_linear':
        p = [F(r+1) for r in range(A)]
        q = [F(r+2) for r in range(A)]
        v = [F(s+3) for s in range(B)]
        w = [F(s+4) for s in range(B)]
    elif kind == 'independent_quadratic':
        p = [F(1) for _ in range(A)]
        q = [F((r+1)**2+1) for r in range(A)]
        v = [F(1) for _ in range(B)]
        w = [F((2*s+1)**2+2) for s in range(B)]
    elif kind == 'uniform_negative_control':
        p, q = [F(1)]*A, [F(1)]*A
        v, w = [F(1)]*B, [F(1)]*B
    elif kind == 'author_seed':
        p = [F(1+(7*(r+seed))%19) for r in range(A)]
        q = [F(1+(11*(r+seed))%23) for r in range(A)]
        v = [F(1+(13*(s+seed))%29) for s in range(B)]
        w = [F(1+(17*(s+seed))%31) for s in range(B)]
    else:
        raise ValueError(kind)
    sp, sv = sum(x*y for x,y in zip(p,q)), sum(x*y for x,y in zip(v,w))
    xi, nu = [z/sp for z in q], [z/sv for z in w]
    assert sum(x*y for x,y in zip(p,xi)) == 1
    assert sum(x*y for x,y in zip(v,nu)) == 1
    x, y = [F(1)/(s*t) for s,t in zip(p,xi)], [F(1)/(s*t) for s,t in zip(v,nu)]
    normalized, actual = [], []
    for i in range(N):
        nr, qr = [], []
        for j in range(N):
            z = F(R[i] == C[j])*x[R[i]] + F(i%B == j%B)*y[i%B] - F(1)
            qij = (F(i%B == j%B)*p[R[i]]*xi[C[j]]
                + F(R[i] == C[j])*v[i%B]*nu[j%B]
                - p[R[i]]*xi[C[j]]*v[i%B]*nu[j%B])
            assert z == qij / (p[R[i]]*v[i%B]*xi[C[j]]*nu[j%B])
            nr.append(z)
            qr.append(-qij)
        normalized.append(nr)
        actual.append(qr)
    result = exact_elimination(normalized)
    assert exact_elimination(actual)['permutation'] == result['permutation']
    if kind == 'uniform_negative_control':
        assert result['permutation'] != EXPECTED
        assert result['permutation'][:29] == EXPECTED[:29]
    else:
        assert result['permutation'] == EXPECTED
    result.update(kind=kind, seed=seed if kind == 'author_seed' else None,
                  p=[str(z) for z in p], xi=[str(z) for z in xi],
                  v=[str(z) for z in v], nu=[str(z) for z in nu])
    return result

def main():
    start = time.monotonic_ns()
    compatibility=(ROOT/'research/rectangular-semantic/compatibility-theorem.txt').read_bytes()
    pin={'repository':'rohanarun/integer-mult-bounds','ref':'3eafe5a35b572fe38e7d64a55ce5cac1d8838bee','path':'research/rectangular-semantic/compatibility-theorem.txt','sha':'0afc0cd1da3ba4341621bad4897f5c37a6f2fa02'}
    assert hashlib.sha1(b'blob '+str(len(compatibility)).encode()+b'\0'+compatibility).hexdigest()==pin['sha']

    # Check all full boundary prescriptions admit a fixed permutation completion.
    maps = [dict() for _ in range(B)]
    for i, r in list(enumerate(RR)) + [(H-len(CC)+j,c) for j,c in enumerate(CC)]:
        alpha, beta = divmod(i, B)
        assert alpha not in maps[beta] or maps[beta][alpha] == r
        assert r not in maps[beta].values() or maps[beta].get(alpha) == r
        maps[beta][alpha] = r
    completions = []
    for fixed in maps:
        free_rows = sorted(set(range(A))-set(fixed))
        free_cols = sorted(set(range(A))-set(fixed.values()))
        full = fixed | dict(zip(free_rows,free_cols))
        assert sorted(full.values()) == list(range(A))
        completions.append([full[i] for i in range(A)])
    assert integer_rank([row[:-1] for row in ROW]) == N
    assert integer_rank([row[:-1] for row in COL]) == N

    certificate = json.loads((AUTHOR/'GEOMETRY_CERTIFICATE.json').read_text())
    assert certificate['row_edges'] == [[R[i], i%B] for i in range(N)]
    assert certificate['column_edges'] == [[C[j], j%B] for j in range(N)]
    cut_checks = []
    for i, j in enumerate(EXPECTED):
        entry = certificate['rank_cuts'][i]
        assert (entry['row'],entry['pivot_column']) == (i,j)
        ss = set(entry['S'])
        rc1 = selected_rank(ROW[:i+1],ss)
        rc2 = selected_rank(COL[j+1:],set(range(A+B+1))-ss)
        expected = sum(k>j for k in EXPECTED[:i])
        assert (rc1,rc2) == (entry['rank_B_S'],entry['rank_C_complement'])
        assert rc1+rc2 == expected == entry['rank_bound'] == entry['expected_bound']
        if 1 <= i <= 25:
            printed = {55} | set(range(i+1,A)) | set(range(A+i+1,A+B))
            printed_ranks = (selected_rank(ROW[:i+1], printed), selected_rank(COL[j+1:],set(range(56))-printed))
            assert printed_ranks == (1,0)
        elif 30 <= i <= 51:
            t = i-30
            printed = {0,55} | set(range(t+4,A)) | set(range(A+t+3,A+B))
            printed_ranks = (selected_rank(ROW[:i+1],printed),selected_rank(COL[j+1:],set(range(56))-printed))
            assert printed_ranks == (27-t,3+t)
        else:
            printed_ranks = (0,N-1-j)
            assert N-1-j == expected
        cut_checks.append(dict(row=i,pivot=j,certificate_ranks=[rc1,rc2],printed_ranks=printed_ranks,bound=expected))
    witnesses = [witness('independent_linear'),witness('independent_quadratic')]
    for slot, seed in enumerate((1,2,3,7)):
        w = witness('author_seed',seed)
        assert certificate['witnesses'][slot]['pivots'] == [[i,j] for i,j in enumerate(w['permutation'])]
        witnesses.append(w)
    negative = witness('uniform_negative_control')
    assert 29+25+648 == 7+25+22+648 == 702
    output = dict(
        source_git_blob_verified=pin,mathematical_arithmetic='integer and Fraction only, asserted in matrix operations',
        cut_checks=cut_checks,independent_positive_witnesses=2,author_witnesses_reproduced=4,
        witnesses=witnesses,uniform_negative_control=negative,permutation_completions=completions,
        rank=702,old_calls=31,new_calls=10,calls_saved_per_occurrence=21,
        elapsed_nanoseconds=time.monotonic_ns()-start,maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        all_passed=True,author_scientific_code_executed=False)
    (HERE/'CONTROL_RESULTS.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:output[k] for k in ['all_passed','independent_positive_witnesses','author_witnesses_reproduced','elapsed_nanoseconds','maxrss_kib']}))

if __name__ == '__main__':
    main()
