"""Propose exact fixed-point integration leaves for the stronger kernel.

Every accepted proposal must subsequently pass the generated Lean arithmetic
and source-binding checks. Floating values choose subdivisions only.
"""
import argparse
import bisect
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import re
import time

S = 2**128
AUX, CAP, ERROR = F(380627425, 10**9), F(380629, 10**6), F(2, 10**12)


def box(q):
    value = F(q)*S
    return value.numerator//value.denominator, -((-value.numerator)//value.denominator)


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def neg(a):
    return -a[1], -a[0]


def sub(a, b):
    return add(a, neg(b))


def scale(a, k):
    return (a[0]*k, a[1]*k) if k >= 0 else (a[1]*k, a[0]*k)


def mul(a, b):
    values = [i*j for i in a for j in b]
    return min(values)//S, -((-max(values))//S)


def horner(coefficients, interval):
    result = (0, 0)
    for coefficient in reversed(coefficients):
        result = add(coefficient, mul(interval, result))
    return result


def positive_line(interval):
    lo, hi = interval
    if hi <= 0:
        return F(0), F(0)
    if lo >= 0:
        return F(0), F(1)
    return F(-lo*hi, S*(hi-lo)), F(hi, hi-lo)


def affine_add(a, b):
    return a[0]+b[0], a[1]+b[1]


def affine_scale(a, c):
    return a[0]*c, a[1]*c


def affine_sub(a, b):
    return affine_add(a, affine_scale(b, -1))


def affine_value(a, x):
    return a[0]+a[1]*x


def capacities(lo, hi):
    middle = (lo+hi)/2
    lower = (2*AUX, F(-1)) if middle < 2*AUX else (F(0), F(0))
    upper = (F(0), F(1)) if middle < CAP else (CAP, F(0))
    clipped = lower if affine_value(lower, middle) <= affine_value(upper, middle) else upper
    return lower, clipped, affine_sub(upper, clipped)


def leaf_weights(kind, boxes, lam, lo, hi):
    ia, ib = boxes[:2]
    if kind == 'Denominator':
        ca, sa = positive_line(ia)
        cb, sb = positive_line(ib)
        return ((2*sa, F(0)), (2*sb, F(0)), (2*(ca+cb), F(0)))
    lower, clipped, excess = capacities(lo, hi)
    bp = 1 if sum(ib) >= 0 else 0
    if kind == 'Central':
        return ((F(0), F(0)), affine_scale(lower, bp), (F(0), F(0)))
    sa, sb = (1 if sum(ia) >= 0 else -1), (1 if sum(ib) >= 0 else -1)
    first_gate = add(sub(box(abs(lam)), scale(ia, sa)), scale(ib, 1-bp))
    second_gate = sub(sub(box(abs(lam)), scale(ia, sa)), scale(ib, sb))
    c1, s1 = positive_line(first_gate)
    c2, s2 = positive_line(second_gate)
    w = affine_add(affine_scale(clipped, s1), affine_scale(excess, s2))
    wa = affine_scale(w, sa)
    wb = affine_add(affine_sub(affine_scale(lower, bp), affine_scale(clipped, (1-bp)*s1)),
                    affine_scale(excess, sb*s2))
    w0 = affine_sub(affine_sub(affine_scale(w, -abs(lam)), affine_scale(clipped, c1)), affine_scale(excess, c2))
    return wa, wb, w0


def weights_integral(weights, boxes, lo, hi):
    wa, wb, w0 = weights
    result = (0, 0)
    for coefficient, interval in zip((wa[0], wa[1], wb[0], wb[1]), boxes[2:]):
        result = add(result, mul(box(coefficient), interval))
    return add(result, add(mul(box(w0[0]), box(hi-lo)), mul(box(w0[1]), box((hi*hi-lo*lo)/2))))


def crossing_error(interval, width):
    return float(F(interval[1]-interval[0], S)*width) if interval[0] < 0 < interval[1] else 0.


def refinement_error(kind, boxes, lam, lo, hi):
    ia, ib = boxes[:2]
    width = hi-lo
    if kind == 'Central':
        return crossing_error(ib, width)
    error = max(crossing_error(ia, 2*width), crossing_error(ib, 2*width))
    if kind != 'Denominator':
        sa, sb, bp = (1 if sum(ia) >= 0 else -1), (1 if sum(ib) >= 0 else -1), (1 if sum(ib) >= 0 else 0)
        g1 = add(sub(box(abs(lam)), scale(ia, sa)), scale(ib, 1-bp))
        g2 = sub(sub(box(abs(lam)), scale(ia, sa)), scale(ib, sb))
        error = max(error, crossing_error(g1, width), crossing_error(g2, width))
    return error


def generate(package, output, tolerance, denominator_tolerance):
    start_time = time.monotonic()
    cert = package/'ErdosOverlap/Certificate'
    frozen = package/'certificates/frontier'
    pieces = [tuple(F(x) for x in row) for row in json.loads((frozen/'affine-pieces.json').read_text())]
    edges = [p[1] for p in pieces]
    old_coefficients = {}
    for path in (cert/'Native6Grid').glob('Coefficients[0-9]*.lean'):
        for index, values in re.findall(r'def coefficients(\d+) : List ℤ := \[([^\]]+)\]', path.read_text()):
            old_coefficients[int(index)] = [int(x) for x in values.split(',')]
    corrections = json.loads((frozen/'correction-coefficients.json').read_text())
    assert len(old_coefficients) == len(corrections) == 1024
    coefficients = [[F(a+b, 2**60) for a, b in zip(old_coefficients[j], corrections[j])] for j in range(1024)]
    raw_kernel = (cert/'FrontierKernelData.lean').read_text()
    def kernel_parameter(name):
        return F(re.search(r'def '+name+r' : ℚ := \(([^:]+) : ℚ\)', raw_kernel)[1].replace(' ', ''))
    y0, y2 = kernel_parameter('y0'), kernel_parameter('y2')
    witnesses = []
    for mode in range(10):
        text = (cert/f'Native6Witness{mode:02d}.lean').read_text()
        nodes = [F(0)]*16385
        for index, value in re.findall(r'⟨(\d+), (\d+)⟩', text.split('theorem')[0]):
            nodes[int(index)] = F(int(value), 10**18)
        tau = F(re.search(r'def tau\d+ : ℚ := \(([^:]+) : ℚ\)', text)[1])
        iv = F(re.search(r'def Iv\d+ : ℚ := \(([^:]+) : ℚ\)', text)[1])
        witnesses.append((nodes, tau, iv))
    for item in json.loads((frozen/'witnesses.json').read_text()):
        witnesses.append(([F(x) for x in item['nodes']], F(item['tau']), F(item['iv_upper'])))
    first_cells = [min(i for i, value in enumerate(nodes) if value)-1 for nodes, tau, iv in witnesses]
    patch_cache, patches, geometries, geometry_index = {}, [], [], {}

    def get_patch(piece, grid):
        key = (piece, grid)
        if key in patch_cache:
            return patch_cache[key]
        center, radius = F(2*grid+1, 1024), F(1, 1024)
        _, _, constant, linear = pieces[piece]
        cs = list(coefficients[grid])
        cs[0] += y0+constant+linear*center+y2*center*center
        cs[1] += radius*(linear+2*y2*center)
        cs[2] += y2*radius*radius
        primitive = [F(0)]+[value/(i+1) for i, value in enumerate(cs)]
        weighted = [F(0), F(0)]+[value/(i+2) for i, value in enumerate(cs)]
        entry = dict(id=len(patches), piece=piece, grid=grid,
                     boxes=[[box(x) for x in values] for values in (cs, primitive, weighted)])
        patches.append(entry)
        patch_cache[key] = entry
        return entry

    def trace(patch, center, radius, lo, hi):
        u, v = (lo-center)/radius, (hi-center)/radius
        inputs = [(box(min(u, v))[0], box(max(u, v))[1]), box(u), box(v)]
        cs, primitive, weighted = patch['boxes']
        values = [horner(cs, inputs[0]), horner(primitive, inputs[1]), horner(primitive, inputs[2]),
                  horner(weighted, inputs[1]), horner(weighted, inputs[2])]
        first, second = sub(values[2], values[1]), sub(values[4], values[3])
        def integral(alpha, beta):
            return mul(box(radius), add(mul(box(alpha+beta*center), first), mul(box(beta*radius), second)))
        return dict(inputs=inputs, values=values), integral(F(1), F(0)), integral(F(0), F(1))

    def get_geometry(lo, hi):
        key = (lo, hi)
        if key in geometry_index:
            return geometries[geometry_index[key]]
        mid = (lo+hi)/2
        piece_a, piece_b, grid = bisect.bisect_right(edges, mid), bisect.bisect_right(edges, 2-mid), int(mid*512)
        assert pieces[piece_a][0] <= lo < hi <= pieces[piece_a][1]
        assert pieces[piece_b][0] <= 2-hi < 2-lo <= pieces[piece_b][1]
        assert F(grid, 512) <= lo and hi <= F(grid+1, 512)
        pa, pb = get_patch(piece_a, grid), get_patch(piece_b, 1023-grid)
        center = F(2*grid+1, 1024)
        ta, ia, ma = trace(pa, center, F(1, 1024), lo, hi)
        tb, ib, mb = trace(pb, center, F(-1, 1024), lo, hi)
        entry = dict(id=len(geometries), left=lo, right=hi, pieceA=piece_a, pieceB=piece_b, grid=grid,
                     patchA=pa['id'], patchB=pb['id'], traceA=ta, traceB=tb,
                     boxes=[ta['values'][0], tb['values'][0], ia, ma, ib, mb])
        geometry_index[key] = entry['id']
        geometries.append(entry)
        return entry

    cuts = {F(0), F(1), AUX, 2*AUX, CAP, 2*AUX-CAP}
    cuts.update(F(i, 512) for i in range(513))
    cuts.update(x for row in pieces for x in row[:2] if 0 < x < 1)
    cuts.update(2-x for row in pieces for x in row[:2] if 1 < x < 2)
    # Outside these tails every actual witness has derivative zero, and its
    # dual slope is 2*tau. Long prefix cells remain unsplit by the witness mesh.
    cuts.update(F(i, 16384) for i in range(min(first_cells[4:]), 16385))
    cuts = sorted(cuts)
    leaves, totals = {}, {}
    for kind in ['Denominator', 'Central']+[f'Profile{i:02d}' for i in range(4, 20)]:
        mode = int(kind[7:]) if kind.startswith('Profile') else None
        accepted, total, subdivisions = [], 0, 0
        for left, right in zip(cuts, cuts[1:]):
            stack = [(left, right, 0)]
            while stack:
                lo, hi, depth = stack.pop()
                g = get_geometry(lo, hi)
                lam, cell = F(0), None
                if mode is not None:
                    nodes, tau, iv = witnesses[mode]
                    cell_index = int((lo+hi)/2*16384)
                    lam = 2*tau+(nodes[cell_index+1]-nodes[cell_index])*16384
                    if hi > F(first_cells[mode], 16384):
                        cell = cell_index-first_cells[mode]
                        assert 0 <= cell < 16384-first_cells[mode]
                        assert F(cell_index, 16384) <= lo < hi <= F(cell_index+1, 16384)
                    else:
                        assert lam == 2*tau
                error = refinement_error(kind, g['boxes'], lam, lo, hi)
                threshold = denominator_tolerance if kind == 'Denominator' else tolerance
                if error > threshold and depth < 32:
                    mid = (lo+hi)/2
                    stack.extend([(mid, hi, depth+1), (lo, mid, depth+1)])
                    subdivisions += 1
                    continue
                weights = leaf_weights(kind, g['boxes'], lam, lo, hi)
                integral = weights_integral(weights, g['boxes'], lo, hi)
                amount = integral[1] if kind == 'Denominator' else integral[0]
                accepted.append(dict(geometry=g['id'], cell=cell, lam=lam, bound=amount))
                total += amount
        assert geometries[accepted[0]['geometry']]['left'] == 0
        assert geometries[accepted[-1]['geometry']]['right'] == 1
        assert all(geometries[a['geometry']]['right'] == geometries[b['geometry']]['left'] for a, b in zip(accepted, accepted[1:]))
        leaves[kind] = accepted
        totals[kind] = F(total, S)+(4*ERROR if kind == 'Denominator' else -2*ERROR)
        print(json.dumps({'kind': kind, 'leaves': len(accepted), 'subdivisions': subdivisions,
                          'bound': float(totals[kind]), 'elapsed_seconds': time.monotonic()-start_time}), flush=True)
    packet = dict(scale=S, approximation_error=ERROR, tolerance=tolerance,
                  denominator_tolerance=denominator_tolerance,
                  patches=patches, geometries=geometries, leaves=leaves, totals=totals,
                  tau=[tau for nodes, tau, iv in witnesses], iv=[iv for nodes, tau, iv in witnesses])
    def encode(value):
        if isinstance(value, F):
            return str(value)
        raise TypeError(type(value))
    output.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(output, 'wt') as stream:
        json.dump(packet, stream, default=encode, separators=(',', ':'))
    print(json.dumps({'packet': str(output), 'geometries': len(geometries), 'patches': len(patches),
                      'elapsed_seconds': time.monotonic()-start_time}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tolerance', type=float, default=2e-12)
    parser.add_argument('--denominator-tolerance', type=float, default=2e-13)
    arguments = parser.parse_args()
    assert arguments.tolerance > 0 and arguments.denominator_tolerance > 0
    generate(arguments.package, arguments.output, arguments.tolerance, arguments.denominator_tolerance)
