"""Recheck saved diagnostic inputs and certificate proof terms without an SMT solver.

The renderer below accepts only the finite arithmetic language used by the saved
cases. Lean checks that each certificate proves the proposition rendered from
its original input, not merely a theorem whose metadata claims success.
"""
from fractions import Fraction
import hashlib
import json
import re

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize(value, variables):
    if isinstance(value, list):
        if value[0] == "^":
            return ["^", normalize(value[1], variables), value[2]]
        return [value[0], *(normalize(x, variables) for x in value[1:])]
    if type(value) is bool or value in variables:
        return value
    return str(Fraction(value))


def render(value, names):
    if type(value) is bool:
        return "True" if value else "False"
    if isinstance(value, str) and value in names:
        return names[value]
    if type(value) is int or isinstance(value, str):
        require(type(value) is int or re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", value),
                "Unsupported rational in diagnostic")
        number = Fraction(value)
        return (f"({number.numerator} : ℝ)" if number.denominator == 1 else
                f"(({number.numerator} : ℝ) / {number.denominator})")
    require(isinstance(value, list) and value, "Unsupported diagnostic expression")
    op, *args = value
    if op == "^":
        require(len(args) == 2 and type(args[1]) is int and 0 <= args[1] <= 8,
                "Unsupported diagnostic power")
        return f"({render(args[0], names)} ^ {args[1]})"
    if op in {"neg", "not"}:
        require(len(args) == 1, "Invalid unary arity")
        return f"({'-' if op == 'neg' else '¬'} {render(args[0], names)})"
    operators = {"+": "+", "-": "-", "*": "*", "=": "=", "!=": "≠",
                 "<": "<", "<=": "≤", ">": ">", ">=": "≥", "and": "∧", "or": "∨"}
    require(op in operators and (len(args) >= 2 if op in {"and", "or"} else len(args) == 2),
            "Unsupported operator or arity")
    return "(" + f" {operators[op]} ".join(render(x, names) for x in args) + ")"


def statements(problem):
    variables = problem["variables"]
    require(len(set(variables)) == len(variables) and all(
        isinstance(v, str) and re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{0,39}", v)
        for v in variables), "Invalid diagnostic variables")
    names = {v: f"v{i}" for i, v in enumerate(variables)}
    assumptions = problem["assumptions"]
    goal = render(problem["goal"], names)
    universal = "".join(f"∀ ({v} : ℝ), " for v in names.values())
    premises = "".join(render(a, names) + " → " for a in assumptions)
    antecedent = "(" + " ∧ ".join(render(a, names) for a in assumptions) + ")" if assumptions else "True"
    existential = "".join(f"∃ ({v} : ℝ), " for v in names.values())
    return {
        "original": universal + premises + goal,
        "valid": universal + premises + goal,
        "false_throughout": universal + premises + f"¬ {goal}",
        "satisfying": existential + f"({antecedent} ∧ {goal})",
        "counterexample": existential + f"({antecedent} ∧ ¬ {goal})",
        "feasible": existential + antecedent,
    }


def read_axioms(log, name):
    match = re.search(re.escape("'" + name + "'") + r" depends on axioms:\s*\[([^]]*)\]", log)
    if match:
        found = [a.strip() for a in match[1].split(",") if a.strip()]
    else:
        require("'" + name + "' does not depend on any axioms" in log, f"Missing axiom audit: {name}")
        found = []
    require(set(found) <= ALLOWED, f"Unapproved axioms for {name}: {found}")
    return found


def prepare(root, cases, uncomment):
    td = root / "verification/theorydebugger"
    environment = json.loads((td / "environment.json").read_text(encoding="utf-8"))
    results = json.loads((td / "results.json").read_text(encoding="utf-8"))
    expected = {name: (status, data) for name, status, data in cases}
    require(len(expected) == len(cases), "Duplicate diagnostic cases")
    require([r["name"] for r in results] == list(expected), "Missing, reordered, or duplicate diagnostic results")
    require(environment["script_sha256"] == digest(root / "scripts/check_theorydebugger.py"), "Diagnostic script hash mismatch")
    require(environment["mathlib_manifest_sha256"] == digest(root / "lake-manifest.json"), "Diagnostic Mathlib hash mismatch")
    input_names = {name + ".json" for name in expected}
    require(set(environment["input_sha256"]) == input_names == {p.name for p in (td / "inputs").glob("*.json")},
            "Diagnostic input inventory mismatch")
    imports, bodies, audits = [], [], []
    certificates = 0
    for result in results:
        name = result["name"]
        status, data = expected[name]
        input_path = td / "inputs" / (name + ".json")
        require(digest(input_path) == environment["input_sha256"][input_path.name], f"Input hash mismatch: {name}")
        saved = json.loads(input_path.read_text(encoding="utf-8"))
        require(saved == {**data, "name": name}, f"Input differs from declared case: {name}")
        problem = {"variables": data["variables"],
                   "assumptions": [normalize(a, data["variables"]) for a in data.get("assumptions", [])],
                   "goal": normalize(data["goal"], data["variables"])}
        require(result["problem"] == problem, f"Result belongs to another problem: {name}")
        require(result["problem_sha256"] == hashlib.sha256(json.dumps(problem, sort_keys=True).encode()).hexdigest(),
                f"Problem identity mismatch: {name}")
        require(result["validity"] == {"status": status, "evidence": "lean_kernel"}, f"Unexpected validity: {name}")
        require(result["consistency"] == {"status": "consistent", "evidence": "lean_kernel"} and not result["warnings"],
                f"Incomplete diagnostic: {name}")
        kinds = [c["kind"] for c in result["certificates"]]
        allowed_kinds = [{"valid", "satisfying"}] if status == "valid" else [
            {"counterexample", "false_throughout"}, {"counterexample", "satisfying"}]
        require(len(kinds) == 2 and set(kinds) in allowed_kinds,
                f"Missing claim or feasibility certificate: {name}")
        classification = "true" if status == "valid" else "mixed" if "satisfying" in kinds else "false"
        require(result["classification"] == classification and result["classification_evidence"] == "lean_kernel",
                f"Classification disagrees with certificate kinds: {name}")
        for side, present in (("satisfying", "satisfying" in kinds), ("refuting", "counterexample" in kinds)):
            require(result["cases"][side]["status"] == ("present" if present else "absent") and
                    result["cases"][side]["evidence"] == "lean_kernel", f"Side evidence mismatch: {name}: {side}")
        targets = statements(problem)
        for cert in result["certificates"]:
            require(cert["status"] == "lean_verified" and cert["compiler_exit_code"] == 0,
                    f"Saved certificate did not succeed: {name}")
            path = (root / cert["source"]).resolve()
            require(path.is_relative_to((td / "certificates").resolve()), "Certificate outside evidence directory")
            require(digest(path) == cert["source_sha256"], f"Certificate hash mismatch: {name}")
            source = path.read_text(encoding="utf-8")
            clean = uncomment(source)
            require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", clean), "Unchecked certificate source")
            require(cert["formal_goal"] == targets["original"], f"Certificate metadata has another goal: {name}")
            prefix = f"Evidence{certificates}"
            body = []
            for line in source.splitlines():
                if line.startswith("import "):
                    require(line.startswith("import Mathlib."), "Certificate imports a local proof")
                    if line not in imports:
                        imports.append(line)
                else:
                    body.append(line)
            # These fresh type checks bind proof terms to the original JSON input.
            # Replacing a source and its hash with an unrelated theorem cannot pass.
            qualified = "TheoryDebugger.Generated."
            checks = [f"example : {qualified}original = ({targets['original']}) := rfl"]
            kind = cert["kind"]
            theorem = {"valid": "claim", "false_throughout": "no_satisfying",
                       "satisfying": "satisfying", "counterexample": "refuting"}[kind]
            checks.append(f"theorem checkedClaim : {targets[kind]} := {qualified}{theorem}")
            checked = ["checkedClaim"]
            if kind in {"satisfying", "counterexample"}:
                checks.append(f"theorem checkedFeasible : {targets['feasible']} := {qualified}feasible")
                checked.append("checkedFeasible")
            for declaration in checked:
                checks.append(f"#print axioms {declaration}")
                audits.append(f"{prefix}.{declaration}")
            bodies.append(f"namespace {prefix}\n" + "\n".join(body + checks) + f"\nend {prefix}\n")
            certificates += 1
    require(len(results) == environment["cases"] and certificates == environment["certificates"], "Evidence counts mismatch")
    # Generated certificates deliberately try alternative arithmetic tactics and
    # quantify every input variable, including irrelevant witness coordinates.
    # Silence only those style warnings; all proof/axiom checks remain enabled.
    options = "\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\nset_option linter.unusedVariables false\n"
    fresh = "\n".join(imports) + options + "\n" + "\n".join(bodies)
    return fresh, audits, len(results), certificates


def verify(root, cases, uncomment, run):
    fresh, declarations, count, certificates = prepare(root, cases, uncomment)
    path = root / "verification/FreshCertificates.lean"
    path.write_text(fresh, encoding="utf-8", newline="\n")
    log = run(path)
    axioms = {name: read_axioms(log, name) for name in declarations}
    return {"cases": count, "certificates": certificates, "saved_evidence_hashes": "passed",
            "fresh_certificate_compilation": "passed", "original_input_type_checks": "passed",
            "fresh_certificates_sha256": digest(path), "axioms": axioms}
