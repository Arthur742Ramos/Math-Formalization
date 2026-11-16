"""Generate the stronger finite cover and its actual physical assembly.

Input assessment is only a proposal: every numerical statement is checked
again in Lean, and integral inequalities come from the checked leaf trees.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import re


def rat(x):
    q = F(x)
    if q.denominator == 1:
        return str(q.numerator)
    return f'({q.numerator}/{q.denominator} : ℚ)'


def generate(package, assessment, template, assembly_template=None):
    report = json.loads(assessment.read_text())
    assert report['pass_proposal'] and len(report['rows']) == 17
    totals = report['totals']
    root = package/'ErdosOverlap'
    text = template.read_text()
    text = text.replace('FrontierEnvelope', 'FrontierCover')
    text = re.sub(r'/-!.*?-/', '/-! Exact finite cover for the source-bound stronger certificate. -/', text, flags=re.S)
    text = re.sub(r'def height : ℚ := .*', f'def height : ℚ := {rat(report["height"])}', text)
    for i, row in enumerate(report['rows']):
        value = f'def native{i:02d} : Row where\n'+''.join(f'  {k} := {rat(row[k])}\n' for k in ['lo','hi','a','b','c','d'])
        text, n = re.subn(rf'def native{i:02d} : Row where\n(?:  .*\n){{6}}', lambda _:value, text)
        assert n == 1, i
    marker = '/-- Source witness: central. -/'
    constants = f'def denominatorBound : ℚ := {rat(totals["Denominator"])}\n'
    constants += f'def centralIntegralLower : ℚ := {rat(totals["Central"])}\n'
    constants += ''.join(f'def profileIntegralLower{i:02d} : ℚ := {rat(totals[f"Profile{i:02d}"])}\n' for i in range(4,20))
    text = text.replace(marker, constants+'\n'+marker)
    (root/'Certificate/FrontierCover.lean').write_text(text)

    kinds = ['Denominator','Central']+[f'Profile{i:02d}' for i in range(4,20)]
    imports = ['ErdosOverlap.Certificate.FrontierCover', 'ErdosOverlap.FrontierIntegralAssembly',
               'ErdosOverlap.Numerics.IntegralClaimFinal',
               'ErdosOverlap.Certificate.CoarseNative6OuterBindings', 'ErdosOverlap.OuterDenominators']
    imports += [f'ErdosOverlap.Certificate.FrontierLeaves.{k}Total' for k in kinds]
    text = ('/-\nCopyright (c) 2026 Erdős overlap formalization contributors.\n'
            'Released under BSD-3-Clause license as described in the file LICENSE.\n-/\nmodule\n\n')
    text += ''.join('public import '+x+'\n' for x in imports)
    text += ('\nnamespace ErdosOverlap.Certificate.FrontierCover\n'
             'open MeasureTheory Set Numerics FrontierLeaves FrontierWitnesses\n'
             'public section\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n')
    text += '''theorem denominator_bound : kernelDenominator Frontier.kernel ≤ (denominatorBound : ℝ) := by
  rw [← integral_denominatorIntegrand]
  exact denominatorCertificate.full_bound (by decide +kernel)

theorem central_integral : (centralIntegralLower : ℝ) ≤ ∫ t in (0 : ℝ)..1, centralIntegrand t :=
  centralCertificate.full_bound (by decide +kernel)

'''
    for i in range(4,20):
        text += f'''theorem profile_integral{i:02d} : (profileIntegralLower{i:02d} : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨{i}, by decide⟩ t :=
  profile{i:02d}Certificate.full_bound (by decide +kernel)

'''
    text += '''theorem nativeRows_physical : PhysicalMeanInequalities nativeRows height := by
  intro r hr
  simp only [nativeRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with '''+' | '.join('rfl' for _ in range(17))+'\n'
    base = '(by decide +kernel)'
    for i, row in enumerate(report['rows']):
        name = row['name']
        if name == 'central':
            text += f'''  · exact (Frontier.centralCertificate native{i:02d} height denominatorBound centralIntegralLower
      {base} {base} {base} {base}
      {base} {base} {base} {base}
      denominator_bound central_integral).physicalMeanInequality
'''
        else:
            mode = int(name[7:])
            text += f'''  · exact (Frontier.profileCertificate native{i:02d} height denominatorBound profileIntegralLower{mode:02d}
      ⟨{mode}, by decide⟩ {base} {base} {base} {base}
      {base} {base} {base} {base}
      denominator_bound profile_integral{mode:02d}).physicalMeanInequality
'''
    original = (assembly_template or package/'certificates/frontier/assembly-template.txt').read_text()
    body = original[original.index('theorem outerRowsNeedingIntegrals_physical'):]
    body = body[:body.index('\nend ErdosOverlap.Certificate.RefinedEnvelope')]
    body = body.replace('(bounds : NativeIntegralBounds)', '')
    body = body.replace('profileRows_physical bounds', 'nativeRows_physical')
    body = body.replace('positiveRows_physical bounds', 'positiveRows_physical')
    body = body.replace('not_overlapCap_of_nonneg_mean bounds', 'not_overlapCap_of_nonneg_mean')
    body = body.replace('not_overlapCap bounds', 'not_overlapCap')
    body = body.replace('peak_gt_height bounds', 'peak_gt_height')
    text += '\nopen CoarseNative6\n\n'+body+'\n\nend\nend ErdosOverlap.Certificate.FrontierCover\n'
    (root/'FrontierVerifiedBound.lean').write_text(text)
    print('Generated source-bound finite cover and physical bound assembly.')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    p.add_argument('--assessment', type=Path, required=True)
    p.add_argument('--template', type=Path,
                   help='Untrusted text template (default: retained certificates/frontier/cover-template.txt)')
    p.add_argument('--assembly-template', type=Path,
                   help='Analytic assembly text (default: retained certificates/frontier/assembly-template.txt)')
    a = p.parse_args()
    generate(a.package, a.assessment, a.template or a.package/'certificates/frontier/cover-template.txt',
             a.assembly_template)
