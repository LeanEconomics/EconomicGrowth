"""Regenerate exact RCK algebra diagnostics and audit their Lean certificates.

This checks polynomial abstractions only. The analytic verification theorem is
proved separately in RamseyCassKoopmans; the solver does not certify ODEs,
infinite integrals, path existence, or convergence.

Usage: python scripts/check_theorydebugger.py [--theorydebugger PATH] [--lake PATH]
Requires the TheoryDebugger source tree and its Python dependencies (including
cvc5), plus the pinned Lean/mathlib dependencies of this project.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

PROJECT = Path(__file__).resolve().parents[1]
WORKSPACE = PROJECT.parent
OUTPUT = PROJECT / "verification" / "theorydebugger"


def fold_binary(op, args):
    result = args[0]
    for arg in args[1:]:
        result = [op, result, arg]
    return result


def add(*args): return fold_binary("+", args)
def sub(a, b): return ["-", a, b]
def mul(*args): return fold_binary("*", args)


def cases():
    """Use exact definitions, rather than hiding multiplication obligations."""
    # TheoryDebugger accepts at most eight variables. Use exact gap variables:
    # V=U0-U1, F=f0-f1, Z=z0-z1, K=k0-k1 and resource gap C=F-Z.
    # The exported Lean theorem checks these substitutions from named equations.
    bdot = add(mul(sub(mul("m", "q"), mul("u", "fprime")), "K"),
               mul("q", sub("Z", mul("m", "K"))))
    ru = sub("V", mul("u", sub("F", "Z")))
    rf = sub("F", mul("fprime", "K"))
    rz = mul(sub("q", "u"), "Z")
    pv_bdot = sub(mul("p", "Z"), mul("w", "u", "fprime", "K"))
    pv_rz = mul(sub("p", mul("w", "u")), "Z")
    base = [[">", "u", 0], [">", "q", 0], [">=", "z", 0],
            ["<=", "q", "u"], ["=", mul(sub("q", "u"), "z"), 0]]
    terminal = [[">", "p", 0], ["<=", "A", mul(-1, "p", sub("k1", "k0"))]]
    return [
        ("cass_pointwise_welfare_identity", "valid", {
            "variables": ["V", "F", "Z", "K", "fprime", "u", "q", "m"],
            "assumptions": [],
            "goal": ["=", "V", sub(add(ru, mul("u", rf), rz), bdot)],
            "witness": {"V": 1, "F": 2, "Z": 0, "K": 1, "fprime": 2, "u": 1, "q": 1, "m": 1}}),
        ("discounted_costate_normalization", "valid", {
            "variables": ["qdot", "d", "m", "q", "u", "fprime"],
            "assumptions": [["=", "qdot", sub(mul(add("d", "m"), "q"), mul("u", "fprime"))]],
            "goal": ["=", sub("qdot", mul("d", "q")), sub(mul("m", "q"), mul("u", "fprime"))],
            "witness": {"qdot": 0, "d": 1, "m": 1, "q": 1, "u": 1, "fprime": 2}}),
        ("present_value_boundary_derivative", "valid", {
            "variables": ["p", "m", "w", "u", "fprime", "K", "Z"], "assumptions": [],
            "goal": ["=", add(mul(sub(mul("m", "p"), mul("w", "u", "fprime")), "K"),
                               mul("p", sub("Z", mul("m", "K")))), pv_bdot],
            "witness": {"p": 1, "m": 1, "w": 1, "u": 1, "fprime": 2, "K": 1, "Z": 0}}),
        ("present_value_welfare_identity", "valid", {
            "variables": ["V", "F", "Z", "K", "fprime", "u", "p", "w"],
            "assumptions": [],
            "goal": ["=", add(mul("w", "V"), pv_bdot),
                     add(mul("w", ru), mul("w", "u", rf), pv_rz)],
            "witness": {"V": 1, "F": 2, "Z": 0, "K": 1, "fprime": 2, "u": 1, "p": 1, "w": 1}}),
        ("corner_does_not_imply_euler_equality", "refuted", {
            "variables": ["u", "q", "z"], "assumptions": base,
            "goal": ["=", "q", "u"], "witness": {"u": 2, "q": 1, "z": 0}}),
        ("interior_implies_euler_equality", "valid", {
            "variables": ["u", "q", "z"], "assumptions": base + [[">", "z", 0]],
            "goal": ["=", "q", "u"], "witness": {"u": 2, "q": 2, "z": 1}}),
        ("complementarity_welfare_term", "valid", {
            "variables": ["u", "q", "z", "otherz"],
            "assumptions": base + [[">=", "otherz", 0]],
            "goal": [">=", mul(sub("q", "u"), sub("z", "otherz")), 0],
            "witness": {"u": 2, "q": 1, "z": 0, "otherz": 1}}),
        ("nonnegative_welfare_remainders", "valid", {
            "variables": ["RU", "RF", "Rz", "u"],
            "assumptions": [[">=", "RU", 0], [">=", "RF", 0], [">=", "Rz", 0], [">", "u", 0]],
            "goal": [">=", add("RU", mul("u", "RF"), "Rz"), 0],
            "witness": {"RU": 1, "RF": 1, "Rz": 1, "u": 1}}),
        ("reversed_terminal_bound_is_invalid", "refuted", {
            "variables": ["A", "p", "k0", "k1"], "assumptions": terminal,
            "goal": ["<=", "A", mul("p", sub("k1", "k0"))],
            "witness": {"A": 1, "p": 1, "k0": 2, "k1": 1}}),
        ("correct_terminal_bound", "valid", {
            "variables": ["A", "p", "k0", "k1"], "assumptions": terminal,
            "goal": ["<=", "A", mul("p", sub("k0", "k1"))],
            "witness": {"A": 1, "p": 1, "k0": 2, "k1": 1}}),
        ("population_weighted_stationary_rate", "valid", {
            "variables": ["d", "m", "rho", "n", "depreciation"],
            "assumptions": [[">", "d", 0], [">", "n", 0], [">", "depreciation", 0],
                            ["=", "d", sub("rho", "n")], ["=", "m", add("n", "depreciation")]],
            "goal": ["=", add("d", "m"), add("rho", "depreciation")],
            "witness": {"d": 1, "m": 2, "rho": 2, "n": 1, "depreciation": 1}}),
    ] + dynamic_cases() + hamiltonian_cases()


def hamiltonian_cases():
    """Local algebra only; the no-path argument is an analytic Lean theorem."""
    velocity = sub("g", "c")
    hdot = add(mul("q", "cd"), mul("qdot", velocity),
               mul("q", sub(mul("gp", velocity), "cd")))
    capacity_h = sub(sub("c", "r"), mul(add(1, mul("r", "r")), "c"))
    return [
        ("hamiltonian_derivative_identity", "valid", {
            "variables": ["q", "cd", "qdot", "g", "c", "gp", "d"],
            "assumptions": [["=", "qdot", mul(sub("d", "gp"), "q")]],
            "goal": ["=", hdot, mul("d", "q", velocity)],
            "witness": {"q": 1, "cd": 0, "qdot": 1, "g": 3, "c": 3, "gp": 0, "d": 1}}),
        ("discounted_hamiltonian_identity", "valid", {
            "variables": ["w", "d", "U", "q", "g", "c"], "assumptions": [],
            "goal": ["=", add(mul(-1, "d", "w", add("U", mul("q", velocity))),
                              mul("w", "d", "q", velocity)), mul(-1, "d", "w", "U")],
            "witness": {"w": 1, "d": 1, "U": "8/3", "q": "10/9", "g": 3, "c": 3}}),
        ("capacity_hamiltonian_negative_identity", "valid", {
            "variables": ["c", "r"],
            "assumptions": [[">", "c", 0], [">", "r", 0], ["=", mul("c", "r"), 1]],
            "goal": ["=", capacity_h, mul(-2, "r")],
            "witness": {"c": 3, "r": "1/3"}}),
        ("capacity_hamiltonian_nonnegative_is_false", "refuted", {
            "variables": ["c", "r"],
            "assumptions": [[">", "c", 0], [">", "r", 0], ["=", mul("c", "r"), 1]],
            "goal": [">=", capacity_h, 0],
            "witness": {"c": 3, "r": "1/3"}}),
    ]


def dynamic_cases():
    """Exact algebra for the constructed square-root Cass path, in both regimes."""
    def power(x, n): return ["^", x, n]
    x2 = power("x", 2)
    z = sub(mul(2, "x"), mul(3, x2))
    r3, r8 = power("r", 3), power("r", 8)
    inner = sub(add(5, mul(5, "r")), add(*(power("r", n) for n in range(2, 7))))
    q = mul("1/10", "s", sub(mul(6, r3), r8))
    qdot = mul("1/10", "s", sub(mul("9/2", r3), mul(2, r8)))
    return [
        ("interior_resource_identity", "valid", {
            "variables": ["x"], "assumptions": [],
            "goal": ["=", add(mul(3, x2), z), mul(2, "x")],
            "witness": {"x": "1/2"}}),
        ("interior_state_dynamics", "valid", {
            "variables": ["x"], "assumptions": [],
            "goal": ["=", mul(2, "x", sub(1, mul(2, "x"))), sub(z, x2)],
            "witness": {"x": "1/2"}}),
        ("interior_investment_threshold", "valid", {
            "variables": ["x"], "assumptions": [[">", "x", 0], ["<=", "x", "2/3"]],
            "goal": [">=", z, 0], "witness": {"x": "1/2"}}),
        ("large_stock_interior_is_not_cass_feasible", "refuted", {
            "variables": ["x"], "assumptions": [[">", "x", "2/3"]],
            "goal": [">=", z, 0], "witness": {"x": 1}}),
        ("corner_costate_identity", "valid", {
            "variables": ["r", "s"], "assumptions": [],
            "goal": ["=", qdot, sub(mul(2, q), mul("1/2", "s", "r", "3/2", power("r", 2)))],
            "witness": {"r": 1, "s": 1}}),
        ("corner_wedge_factorization", "valid", {
            "variables": ["r"], "assumptions": [],
            "goal": ["=", add(sub(mul(5, "r"), mul(6, r3)), r8),
                     mul("r", sub(1, "r"), inner)], "witness": {"r": 1}}),
        ("corner_wedge_product_nonnegative", "valid", {
            "variables": ["r", "B"],
            "assumptions": [[">=", "r", 0], ["<=", "r", 1], [">=", "B", 0]],
            "goal": [">=", mul("r", sub(1, "r"), "B"), 0],
            "witness": {"r": "1/2", "B": 1}}),
        ("switch_capital_derivatives_match", "valid", {
            "variables": ["x"], "assumptions": [["=", "x", "2/3"]],
            "goal": ["=", mul(2, "x", sub(1, mul(2, "x"))), mul(-1, x2)],
            "witness": {"x": "2/3"}}),
        ("corner_consumption_does_not_satisfy_interior_euler", "refuted", {
            "variables": ["r"], "assumptions": [[">", "r", 0], ["<=", "r", 1]],
            "goal": ["=", "-1/2", sub(mul(3, power("r", 2)), 4)],
            "witness": {"r": 1}}),
    ]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--theorydebugger", type=Path, default=WORKSPACE / "TheoryDebugger")
    default_lake = WORKSPACE / ".tools" / "elan" / "bin" / "lake.exe"
    parser.add_argument("--lake", default=str(default_lake) if default_lake.exists() else "lake")
    args = parser.parse_args()
    td = args.theorydebugger.resolve()
    if not (td / "src" / "theorydebugger" / "diagnose.py").is_file():
        parser.error("--theorydebugger must identify a TheoryDebugger source checkout")
    local_elan = WORKSPACE / ".tools" / "elan"
    if local_elan.exists():
        os.environ.setdefault("ELAN_HOME", str(local_elan))
    sys.path.insert(0, str(td / "src"))
    from theorydebugger.backend import CVC5Backend
    from theorydebugger.certificates import LeanVerifier
    from theorydebugger.diagnose import diagnose
    from theorydebugger.ir import parse
    import cvc5

    inputs = OUTPUT / "inputs"
    inputs.mkdir(parents=True, exist_ok=True)
    verifier = LeanVerifier(PROJECT, OUTPUT / "certificates", args.lake)
    records = []
    for name, expected, data in cases():
        data["name"] = name
        (inputs / (name + ".json")).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8", newline="\n")
        result = diagnose(parse(data), CVC5Backend(), verifier)
        for certificate in result["certificates"]:
            for field in ("source", "compiler_log"):
                if field in certificate:
                    certificate[field] = Path(certificate[field]).relative_to(PROJECT).as_posix()
        records.append(result)
        (OUTPUT / "results.json").write_text(json.dumps(records, indent=2, default=str) + "\n", encoding="utf-8", newline="\n")
        print(name, result["validity"], result["consistency"], flush=True)
        if result["validity"] != {"status": expected, "evidence": "lean_kernel"}:
            raise RuntimeError(json.dumps(result, indent=2, default=str))
        if result["consistency"] != {"status": "consistent", "evidence": "lean_kernel"}:
            raise RuntimeError("Assumption feasibility was not checked")
        if result["warnings"] or any(c["status"] != "lean_verified" for c in result["certificates"]):
            raise RuntimeError("Incomplete or rejected certificate")
    environment = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Twenty-four polynomial abstractions only; analytic theorems are checked separately by lake build.",
        "lean": subprocess.check_output([args.lake, "env", "lean", "--version"], cwd=PROJECT, text=True).strip(),
        "cvc5": cvc5.Solver().getVersion().decode(),
        "mathlib_manifest_sha256": digest(PROJECT / "lake-manifest.json"),
        "script_sha256": digest(Path(__file__)),
        "theorydebugger_source_sha256": {p.relative_to(td).as_posix(): digest(p) for p in sorted((td / "src" / "theorydebugger").glob("*.py"))},
        "cases": len(records), "certificates": sum(len(r["certificates"]) for r in records),
        "input_sha256": {p.name: digest(p) for p in sorted(inputs.glob("*.json"))},
    }
    (OUTPUT / "environment.json").write_text(json.dumps(environment, indent=2) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
