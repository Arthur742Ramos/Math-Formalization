#!/usr/bin/env python3
"""Assemble fixed public source bodies without solution-module imports."""
from pathlib import Path
import sys

if not __debug__ or sys.flags.optimize:
    raise SystemExit('Challenge assembly checks refuse assertion-disabled Python optimization modes')

MODULES = ['SparseCompletion', 'MomentCompression', 'GameModel', 'SparseWitness', 'GameSparseWitness', 'CompletionDual', 'CompletionGeometry', 'CompletionCriterion', 'SparseCompletionWitness', 'PaperWitness', 'PrefixRigidity', 'TwoAnchorRigidity', 'MinimumShareRigidity', 'PrefixStability', 'MinimumShareStability', 'Quantization', 'SupportQuantization', 'SupportLowerBound', 'SupportRate', 'SupportMinimum', 'ResidualMinimum', 'IntervalLower', 'CoreLower', 'BinCompression', 'BinnedWitness', 'BalancedBins', 'BinnedCompletion', 'BinnedMoments', 'BinnedGame', 'BalancedGame', 'CoreAdjustment', 'NoiseUpper', 'NoiseSharp', 'MidpointExact', 'BinnedExact', 'MidpointGame', 'BalancedExact', 'AllMassWitness', 'ExtraMomentCuts', 'ExtraMomentGameCertificates', 'ExtraMomentCompletion', 'ExtraMomentWitness', 'ExtraMomentAllMass', 'ScorePrefixes', 'ConicCompletion', 'ConicConvexity', 'IntervalPerspective', 'IntervalConic', 'ObservationCover', 'CoveredWitness', 'IntervalProjection', 'WeakCover', 'WeakCoverWitness', 'IntervalLossMaximum', 'WeakCoverMaximum', 'CoverRelabel', 'ArbitraryCover', 'ArbitraryWeakCover', 'IntervalLossOrder', 'IntervalConvexity', 'GapCertificates', 'GapFeasibility', 'IntervalRepertoire', 'IntervalStability', 'OptimisticValue', 'ValueStability', 'SupportCompact', 'OrderedStability', 'ThresholdSeparation', 'IntervalSeparation', 'JointSupportFoundation', 'JointSupportLower', 'JointSupportUpper', 'JointSupportTheorem', 'JointSupportGeneral', 'RationalCertificate', 'RationalCertificateSoundness', 'FixedValue', 'GapCompact', 'ValueBounds', 'GapValue', 'AllocationRounding', 'AllocationGrid', 'AllocationResponse', 'AllocationValue', 'AllocationApproximation', 'IntervalGap', 'IntervalGapGame', 'Bisection', 'IntervalGapEpigraph', 'GapSparse', 'IntervalGapSparse', 'RationalGrid', 'RationalGridSizeBounds', 'RationalGap']

def assemble(root):
    imports, bodies = [], []
    for name in MODULES:
        body = []
        for line in (root/(name+'.lean')).read_text().splitlines(keepends=True):
            if line.strip() == 'module':
                continue
            if line.startswith('public import '):
                imported = line.removeprefix('public import ').strip()
                if imported not in MODULES and imported not in imports:
                    imports.append(imported)
                continue
            body.append(line)
        bodies.append('\n/- Fixed source body: '+name+'.lean -/\n'+''.join(body))
    return 'module\n'+''.join('public import '+name+'\n' for name in imports)+'\n'+''.join(bodies)

if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    text = assemble(root)
    if '--check' in sys.argv:
        assert (root/'SECChallenge.lean').read_text() == text
    else:
        (root/'SECChallenge.lean').write_text(text)
