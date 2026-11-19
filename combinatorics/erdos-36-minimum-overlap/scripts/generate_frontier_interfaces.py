"""Instantiate the existing analytic leaf interfaces for the new sources.

The underlying arithmetic and soundness proofs are retained. This changes
their explicit kernel, witness family, piece table, polynomial coefficients,
and approximation allowance; all resulting modules must elaborate in Lean.
"""
import argparse
import json
from pathlib import Path


def generate(package):
    root = package/'ErdosOverlap'
    count = len(json.loads((package/'certificates/frontier/affine-pieces.json').read_text()))
    pairs = [
        ('NativePolynomialPatchActual', 'FrontierPolynomialPatchActual'),
        ('NativeLeafGeometryActual', 'FrontierLeafGeometryActual'),
        ('NativeLeafGeometry', 'FrontierLeafGeometry'),
        ('NativePolynomialCache', 'FrontierPolynomialCache'),
        ('NativePolynomialDirectTrace', 'FrontierPolynomialDirectTrace'),
        ('NativeLeafCertificateData', 'FrontierLeafCertificateData'),
        ('NativeLeafCapacities', 'FrontierLeafCapacities'),
        ('NativeLeafCertificateActual', 'FrontierLeafCertificateActual'),
        ('NativeLeafCertificate', 'FrontierLeafCertificate'),
        ('NativeLeafAssemblyActual', 'FrontierLeafAssemblyActual'),
        ('NativeLeafAssembly', 'FrontierLeafAssembly'),
    ]
    for original, name in pairs:
        text = (root/'Numerics'/f'{original}.lean').read_text()
        for old, new in pairs:
            text = text.replace(f'ErdosOverlap.Numerics.{old}', f'ErdosOverlap.Numerics.{new}')
        text = text.replace('ErdosOverlap.Native6Leaves', 'ErdosOverlap.FrontierLeaves')
        text = text.replace('Native6Jumps', 'FrontierJumps')
        text = text.replace('Native6Witnesses', 'FrontierWitnesses')
        text = text.replace('ErdosOverlap.Native6WitnessModeFacts', 'ErdosOverlap.FrontierWitnessModeFacts')
        text = text.replace('ErdosOverlap.Certificate.Native6WitnessSlopes', 'ErdosOverlap.FrontierWitnessModeFacts')
        text = text.replace('Native6Data.y0', 'FrontierData.y0').replace('Native6Data.y2', 'FrontierData.y2')
        text = text.replace('Native6.', 'Frontier.')
        text = text.replace('Fin 10', 'Fin 20').replace('6361', str(count))
        text = text.replace('ErdosOverlap.Certificate.Native6AffineData', 'ErdosOverlap.Certificate.FrontierPieceData')
        text = text.replace('ErdosOverlap.Certificate.Native6KernelData', 'ErdosOverlap.Certificate.FrontierKernelData')
        text = text.replace('ErdosOverlap.Certificate.Native6Grid.CoefficientRows', 'ErdosOverlap.Numerics.FrontierPolynomialData')
        text = text.replace('(quantizedCoefficients (Native6Grid.coefficientRow g.grid))', '(FrontierGrid.combinedCoefficients g.grid)')
        text = text.replace('(quantizedCoefficients (Native6Grid.coefficientRow (1023-g.grid)))', '(FrontierGrid.combinedCoefficients (1023-g.grid))')
        text = text.replace('(quantizedCoefficients (Native6Grid.coefficientRow grid))', '(FrontierGrid.combinedCoefficients grid)')
        if original == 'NativePolynomialPatchActual':
            text = text.replace('ErdosOverlap.Native6AffineKernel', 'ErdosOverlap.FrontierAffineKernel')
            text = text.replace('ErdosOverlap.Certificate.Native6Grid.UniformError', 'ErdosOverlap.Numerics.FrontierPolynomial')
            text = text.replace('ErdosOverlap.Native6Grid', 'ErdosOverlap.FrontierGrid')
            text = text.replace('(quantizedCoefficients (coefficientRow j))', '(combinedCoefficients j)')
            text = text.replace('cosineSum Native6Trig.terms', 'cosineSum FrontierTrig.terms')
            text = text.replace('cosine_uniform_error_on_interval', 'combined_cosine_uniform_error_on_interval')
        if original == 'NativeLeafGeometryActual':
            text = text.replace('Native6Grid.nativePolynomialPiece', 'FrontierGrid.nativePolynomialPiece')
            text = text.replace('Native6Grid.nativePolynomialPieceAt', 'FrontierGrid.nativePolynomialPieceAt')
        if original == 'NativeLeafCertificateData':
            text = text.replace('def approximationError : ℚ := 1/1000000000000', 'def approximationError : ℚ := 2/1000000000000')
        if original in ('NativeLeafGeometryActual', 'NativePolynomialPatchActual', 'NativeLeafCertificateActual'):
            text = text.replace('(1 / 1000000000000 : ℝ)', '(2 / 1000000000000 : ℝ)')
        if original == 'NativeLeafCertificate':
            text = text.replace('public import ErdosOverlap.KernelIntegrability',
                                'public import ErdosOverlap.KernelIntegrability\npublic import ErdosOverlap.FrontierKernel')
        (root/'Numerics'/f'{name}.lean').write_text(text)
        print(name)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    generate(p.parse_args().package)
