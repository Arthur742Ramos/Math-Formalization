"""Check the pinned, unmodified definition dossier without building dependencies."""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MATHLIB = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
LEAN = "11acb17ec6b07a8f9e9173e6845197929540936b"
MATERIAL = {'subtype topology', 'PreconnectedSpace', 'Composants.IsPartitionBetween', 'IsNowhereDense', 'Set.preimage', 'interior', 'closure', 'IsClosed', 'T2Space', 'Set.Countable', 'Set.range', 'Composants.IsIndecomposable', 'Composants.IsOmegaMap', 'TopologicalSpace.induced', 'UniformSpace', 'IsOpen', 'Set.instCompleteAtomicBooleanAlgebra', 'Dist', 'MetricSpace', 'Nontrivial', 'Composants.IsContinuum', 'ConnectedSpace', 'PseudoMetricSpace', 'Set.sUnion', 'Composants.composant', 'CompactSpace', 'Composants.IsOpenCover', 'IsPreconnected', 'IsCompact', 'TopologicalSpace', 'IsMeagre', 'SecondCountableTopology', 'Disjoint', 'Continuous', 'Function.Surjective', 'Composants.IsSubcontinuum', 'IsConnected', 'Dense', 'Nonempty'}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_end(lines: list[str], start_line: int) -> int:
    """End of an indexed top-level declaration in these pinned source files.

    Continuation lines are indented or begin an attached `deriving` or `where`
    block. Blank lines inside a declaration are retained; trailing blank lines
    and the next top-level command are excluded.
    This is a bounded source-layout check, not a general Lean parser.
    """
    assert 1 <= start_line <= len(lines), "declaration start"
    end = start_line
    while end < len(lines) and (
            not lines[end].strip() or lines[end][0].isspace()
            or re.match(r"^(?:deriving|where)\b", lines[end])):
        end += 1
    while not lines[end - 1].strip():
        end -= 1
    return end


def validate(manifest: dict, data: dict[str, bytes]) -> None:
    assert manifest["mathlib_commit"] == MATHLIB, "Mathlib revision"
    assert manifest["lean_commit"] == LEAN, "Lean revision"
    assert manifest["lean_toolchain"] == data["lean-toolchain"].decode().strip(), "toolchain"
    lock = json.loads(data["lake-manifest.json"])
    assert next(p for p in lock["packages"] if p["name"] == "mathlib")["rev"] == MATHLIB
    assert set(manifest["material_statement_predicates"]) == MATERIAL, "predicate inventory"
    assert set(manifest["frozen_sources"]) == {'Challenge.lean', 'Foundations.lean', 'Boundary.lean', 'Alexandroff.lean', 'Interior.lean', 'Solution.lean'}, "frozen source inventory"
    for name, sha in manifest["frozen_sources"].items():
        assert digest(data[name]) == sha, "frozen source " + name

    indexed = {d["name"] for d in manifest["definitions"]}
    assert MATERIAL - {'Composants.composant', 'Composants.IsIndecomposable', 'Composants.IsSubcontinuum'} <= indexed, "missing predicate definition"
    for source in manifest["sources"]:
        raw = data[source["file"]]
        assert len(raw) == source["bytes"] and digest(raw) == source["sha256"], source["file"]
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        assert blob == source["git_blob"], "Git blob " + source["file"]
        expected_pin = LEAN if source["repository"] == "leanprover/lean4" else MATHLIB
        assert source["commit"] == expected_pin and source["license"] == "Apache-2.0"
        assert source["source_url"] == (
            f"https://github.com/{source['repository']}/blob/{expected_pin}/{source['upstream_path']}")
    for definition in manifest["definitions"]:
        lines = data[definition["file"]].decode().splitlines(keepends=True)
        assert definition["end_line"] == declaration_end(lines, definition["start_line"]), (
            "incomplete or overextended declaration " + definition["name"])
        excerpt = "".join(lines[definition["start_line"] - 1:definition["end_line"]]).encode()
        assert digest(excerpt) == definition["excerpt_sha256"], definition["name"]
        assert set(definition["depends_on"]) <= indexed, "unresolved cross-reference " + definition["name"]
    countable_generate = next(d for d in manifest["definitions"]
                              if d["name"] == "Filter.countableGenerate")
    assert (countable_generate["start_line"], countable_generate["end_line"]) == (281, 283), (
        "pinned countableGenerate range must include deriving")
    lines = data[countable_generate["file"]].decode().splitlines()
    assert lines[282] == "deriving CountableInterFilter", "pinned deriving tail"
    for name in manifest["literal_excerpts"]:
        definition = next(d for d in manifest["definitions"] if d["name"] == name)
        lines = data[definition["file"]].decode().splitlines(keepends=True)
        excerpt = "".join(lines[definition["start_line"] - 1:definition["end_line"]])
        assert "```lean\n" + excerpt + "```" in data["DEFINITIONS.md"].decode(), "documentation excerpt " + name


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare-mathlib", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "definition-evidence/manifest.json").read_text())
    names = [s["file"] for s in manifest["sources"]]
    names += list(manifest["frozen_sources"]) + ["lean-toolchain", "lake-manifest.json", "DEFINITIONS.md"]
    data = {name: (ROOT / name).read_bytes() for name in names}
    validate(manifest, data)
    compared = 0
    if args.compare_mathlib:
        for source in manifest["sources"]:
            if source["repository"] != "leanprover-community/mathlib4" or source["upstream_path"] == "LICENSE":
                continue
            installed = ROOT / ".lake/packages/mathlib" / source["upstream_path"]
            assert installed.read_bytes() == data[source["file"]], "installed dependency " + source["upstream_path"]
            compared += 1
    if args.self_test:
        bad_data = dict(data)
        bad_data[manifest["sources"][0]["file"]] += b" "
        bad_pin = copy.deepcopy(manifest)
        bad_pin["mathlib_commit"] = "0" * 40
        bad_index = copy.deepcopy(manifest)
        bad_index["definitions"] = [d for d in bad_index["definitions"] if d["name"] != "IsPreconnected"]
        bad_excerpt = copy.deepcopy(manifest)
        truncated_data = dict(data)
        connected = next(d for d in bad_excerpt["definitions"] if d["name"] == "IsConnected")
        lines = data[connected["file"]].decode().splitlines(keepends=True)
        complete = "".join(lines[connected["start_line"] - 1:connected["end_line"]])
        header = lines[connected["start_line"] - 1]
        connected["end_line"] = connected["start_line"]
        connected["excerpt_sha256"] = digest(header.encode())
        truncated_data["DEFINITIONS.md"] = data["DEFINITIONS.md"].replace(complete.encode(), header.encode())
        def omit_tail(name: str) -> tuple[dict, dict[str, bytes]]:
            candidate = copy.deepcopy(manifest)
            payload = dict(data)
            declaration = next(d for d in candidate["definitions"] if d["name"] == name)
            lines = data[declaration["file"]].decode().splitlines(keepends=True)
            complete = "".join(lines[declaration["start_line"] - 1:declaration["end_line"]])
            declaration["end_line"] -= 1
            shortened = "".join(lines[declaration["start_line"] - 1:declaration["end_line"]])
            declaration["excerpt_sha256"] = digest(shortened.encode())
            payload["DEFINITIONS.md"] = data["DEFINITIONS.md"].replace(complete.encode(), shortened.encode())
            return candidate, payload
        omitted_set, set_data = omit_tail("Set.instCompleteAtomicBooleanAlgebra")
        omitted_metric, metric_data = omit_tail("MetricSpace")
        omitted_pseudo, pseudo_data = omit_tail("PseudoMetricSpace")
        omitted_refinement, refinement_data = omit_tail("Composants.IsOmegaMap")
        omitted_deriving, deriving_data = omit_tail("Filter.countableGenerate")
        omitted_where, where_data = omit_tail("TopologicalSpace")
        # These bounded layout fixtures exercise unindented attached blocks.
        assert declaration_end(["def sample := 0\n", "where\n", "  helper := 0\n",
                                "deriving SampleClass\n", "\n", "def next := 1\n"], 1) == 4
        failures = []
        for label, candidate, payload in [
                ("corrupt source", manifest, bad_data), ("changed pin", bad_pin, data),
                ("missing definition", bad_index, data),
                ("header-only IsConnected with matching hash and prose", bad_excerpt, truncated_data),
                ("omitted deriving tail with matching hash and prose", omitted_deriving, deriving_data),
                ("omitted where-block field with matching hash and prose", omitted_where, where_data),
                ("omitted metric separation field", omitted_metric, metric_data),
                ("omitted compatible metric structure field", omitted_pseudo, pseudo_data),
                ("omitted inverse-image refinement body", omitted_refinement, refinement_data),
                ("omitted native set-order instance field", omitted_set, set_data)]:
            try:
                validate(candidate, payload)
            except AssertionError as error:
                failures.append({"control": label, "rejection": str(error)})
                continue
            raise AssertionError("negative control accepted")
    print(json.dumps({"status": "pass", "source_files": len(manifest["sources"]),
                      "indexed_definitions": len(manifest["definitions"]),
                      "installed_mathlib_files_compared": compared,
                      "complete_declaration_ranges": len(manifest["definitions"]),
                      "negative_controls_rejected": 10 if args.self_test else 0,
                      "negative_control_results": failures if args.self_test else []}))


if __name__ == "__main__":
    main()
