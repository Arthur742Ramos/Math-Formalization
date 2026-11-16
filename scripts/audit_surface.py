"""Text-level statement and small finite-instance checks; not a Lean replay."""

from itertools import combinations
from pathlib import Path
import json
import re
import sys

ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
challenge = (ROOT / "Challenge.lean").read_text()
defs = {
    "Admissible": "ErdosOverlap/Overlap.lean",
    "positiveOverlap": "ErdosOverlap/Overlap.lean",
    "negativeOverlap": "ErdosOverlap/Overlap.lean",
    "overlapValues": "ErdosOverlap/Constant.lean",
    "overlapPeak": "ErdosOverlap/Constant.lean",
    "relaxedPeaks": "ErdosOverlap/Constant.lean",
    "relaxedOverlapConstant": "ErdosOverlap/Constant.lean",
    "BinaryAdmissible": "ErdosOverlap/Constant.lean",
    "partitionPeaks": "ErdosOverlap/Constant.lean",
    "erdosOverlapConstant": "ErdosOverlap/Constant.lean",
    "differenceCount": "ErdosOverlap/DiscreteCorrelation.lean",
    "maximumCount": "ErdosOverlap/DiscreteCorrelation.lean",
    "BalancedPartition": "ErdosOverlap/DiscreteDensity.lean",
    "finiteMaximumValues": "ErdosOverlap/DiscreteProblem.lean",
    "minimumOverlap": "ErdosOverlap/DiscreteProblem.lean",
    "minimumOverlapQuotient": "ErdosOverlap/DiscreteProblem.lean",
    "discreteOverlapConstant": "ErdosOverlap/DiscreteProblem.lean",
}


def get_block(text, name):
    pattern = (r"(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
               r"(?:def|structure)\s+" + re.escape(name) + r"\b")
    match = re.search(pattern, text)
    if not match:
        raise ValueError(f"missing definition {name}")
    end = text.find("\n\n", match.start())
    return text[match.start():end if end >= 0 else len(text)]


def normalize(text):
    text = re.sub(r"@\[[^\]]*\]", "", text)
    text = re.sub(r"\bnoncomputable\b", "", text)
    return re.sub(r"\s+", "", text)


def theorem_type(text, name):
    match = re.search(r"(?ms)^theorem\s+" + re.escape(name) + r"\b(.*?):=", text)
    if not match:
        raise ValueError(f"missing theorem {name}")
    return normalize(match.group(1))


def finite_sanity(limit):
    rows = []
    for n in range(1, limit + 1):
        universe = tuple(range(1, 2*n + 1))
        minimum = None
        for left in combinations(universe, n):
            left_set = set(left)
            right = [x for x in universe if x not in left_set]
            counts = [0] * (4*n + 1)
            for a in left:
                for b in right:
                    counts[a-b+2*n] += 1
            peak = max(counts)
            minimum = peak if minimum is None else min(minimum, peak)
        if minimum * 10_000_000_000 <= 3_806_279_907 * n:
            raise AssertionError(f"finite headline fails at N={n}")
        rows.append({"N": n, "minimum_count": minimum,
                     "partitions_checked": __import__("math").comb(2*n, n)})
    return rows


def main():
    problems = []
    legacy = (ROOT / "NumericChallenge.lean").read_text()
    for name, file in defs.items():
        reference = (ROOT / file).read_text()
        if normalize(get_block(challenge, name)) != normalize(get_block(reference, name)):
            problems.append(f"definition mismatch: {name}")
        if normalize(get_block(legacy, name)) != normalize(get_block(reference, name)):
            problems.append(f"NumericChallenge definition mismatch: {name}")

    config = json.loads((ROOT / "comparator.json").read_text())
    if config['definition_names'] != []:
        problems.append('Fixed model definitions must not be definition holes')
    fixed = json.loads((ROOT / 'verification/fixed-definitions.json').read_text())
    continuous = list(defs)[:10]
    discrete = list(defs)[10:]
    expected_fixed = {'ErdosOverlap.'+name for name in continuous if name != 'Admissible'}
    expected_fixed.update('ErdosOverlap.Discrete.'+name for name in discrete if name != 'BalancedPartition')
    if fixed.get('schema_version') != 1 or len(fixed['fixed_definition_names']) != 15 or set(fixed['fixed_definition_names']) != expected_fixed:
        problems.append('Fixed-definition inventory differs from the actual model definitions')
    proof = (ROOT / "ErdosOverlap/VerifiedBound.lean").read_text() + "\n" + (ROOT / "ErdosOverlap/DefinitionContracts.lean").read_text()
    for qualified in config["theorem_names"]:
        name = qualified.rsplit(".", 1)[-1]
        if theorem_type(challenge, name) != theorem_type(proof, name):
            problems.append(f"theorem signature mismatch: {name}")
        if theorem_type(legacy, name) != theorem_type(proof, name):
            problems.append(f"NumericChallenge theorem signature mismatch: {name}")

    imports = re.findall(r"(?m)^public import\s+(\S+)", challenge)
    if not imports or any(not item.startswith("Mathlib.") for item in imports):
        problems.append("Challenge has a non-Mathlib import")

    result = {
        "scope": "Text comparison and exhaustive finite sanity checks; not Lean or Comparator verification.",
        "definitions_compared": len(defs),
        "fixed_model_definitions": len(expected_fixed),
        "theorem_signatures_compared": len(config["theorem_names"]),
        "statement_surfaces": ["Challenge", "NumericChallenge"],
        "challenge_imports": imports,
        "issues": problems,
        "finite_sanity": finite_sanity(9),
    }
    print(json.dumps(result, indent=2))
    if problems:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
