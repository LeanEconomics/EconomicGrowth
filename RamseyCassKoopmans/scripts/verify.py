"""Build, freshly elaborate original Lean source, and audit declaration axioms."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def uncomment(source):
    """Remove nested Lean block comments and line comments for declaration scanning."""
    out, index, depth = [], 0, 0
    while index < len(source):
        pair = source[index:index + 2]
        if pair == "/-":
            depth += 1
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            index += 2
        elif not depth and pair == "--":
            end = source.find("\n", index)
            index = len(source) if end == -1 else end
        else:
            char = source[index]
            out.append(char if not depth or char == "\n" else " ")
            index += 1
    assert depth == 0, "Unclosed Lean comment"
    return "".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    args = parser.parse_args()
    config = json.loads((ROOT / "proof-manifest.json").read_text(encoding="utf-8"))
    inventory = {p.relative_to(ROOT).as_posix() for p in
                 (ROOT / "RamseyCassKoopmans").rglob("*.lean")}
    assert set(config["modules"]) == inventory, "Proof manifest must cover every library module"
    root_imports = {line.removeprefix("import ").replace(".", "/") + ".lean"
                    for line in (ROOT / "RamseyCassKoopmans.lean").read_text().splitlines()
                    if line.startswith("import RamseyCassKoopmans.")}
    assert root_imports == inventory, "Root library must import every audited module"
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)

    def run(command, filename):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                encoding="utf-8", errors="replace", timeout=1200)
        log = result.stdout + result.stderr
        (out / filename).write_text(log, encoding="utf-8", newline="\n")
        if result.returncode or any(token in log for token in
                                   ("error:", "error(", "PANIC", "sorryAx", "warning:")):
            raise RuntimeError(log)
        return log

    imports, bodies, declarations, counts, hashes = [], [], [], {}, {}
    for module in config["modules"]:
        path = ROOT / module
        raw = path.read_text(encoding="utf-8")
        hashes[module] = digest(path)
        clean = uncomment(raw)
        if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", clean):
            raise RuntimeError(f"Unaccepted placeholder, axiom or unchecked evaluator in {module}")
        namespaces, count = [], 0
        for line in clean.splitlines():
            line = line.strip()
            if line.startswith("namespace "):
                namespaces.append(line[len("namespace "):].strip())
            elif line.startswith("end "):
                assert namespaces, (module, line)
                assert namespaces[-1] == line[len("end "):].strip(), (module, line)
                namespaces.pop()
            elif match := re.match(r"(?:noncomputable )?(theorem|lemma|def|abbrev) ([\w.']+)", line):
                name = ".".join(namespaces + [match[2]])
                declarations.append({"name": name, "kind": match[1], "module": module})
                count += match[1] in ("theorem", "lemma")
        assert not namespaces, (module, namespaces)
        counts[module] = count
        body = []
        for line in raw.splitlines():
            if line.startswith("import "):
                if not line.startswith("import RamseyCassKoopmans") and line not in imports:
                    imports.append(line)
            else:
                body.append(line)
        bodies.append("\n".join(body))
    assert counts == config["theorem_counts"], (counts, config["theorem_counts"])
    assert len({d["name"] for d in declarations}) == len(declarations)
    fresh = "\n".join(imports) + "\nset_option autoImplicit false\n\n" + "\n\n".join(bodies)
    fresh += "\n\n" + "\n".join("#print axioms " + d["name"] for d in declarations) + "\n"
    freshpath = out / "FreshAudit.lean"
    freshpath.write_text(fresh, encoding="utf-8", newline="\n")
    run([args.lake, "build"], "build.txt")
    log = run([args.lake, "env", "lean", str(freshpath)], "fresh-audit.txt")
    axioms = {}
    for decl in declarations:
        name = decl["name"]
        match = re.search(re.escape("'" + name + "'") + r" depends on axioms:\s*\[([^]]*)\]", log)
        if match:
            found = [a.strip() for a in match[1].split(",") if a.strip()]
        else:
            assert "'" + name + "' does not depend on any axioms" in log, name
            found = []
        assert set(found) <= ALLOWED, (name, found)
        axioms[name] = found

    # Validate saved TheoryDebugger evidence against its source/input hashes.
    td = out / "theorydebugger"
    environment = json.loads((td / "environment.json").read_text(encoding="utf-8"))
    results = json.loads((td / "results.json").read_text(encoding="utf-8"))
    assert environment["script_sha256"] == digest(ROOT / "scripts/check_theorydebugger.py")
    assert environment["mathlib_manifest_sha256"] == digest(ROOT / "lake-manifest.json")
    for name, expected in environment["input_sha256"].items():
        assert digest(td / "inputs" / name) == expected, name
    certificate_count = 0
    for result in results:
        assert result["validity"]["evidence"] == "lean_kernel"
        assert result["consistency"] == {"status": "consistent", "evidence": "lean_kernel"}
        assert not result["warnings"]
        for certificate in result["certificates"]:
            assert certificate["status"] == "lean_verified"
            assert certificate["compiler_exit_code"] == 0
            for declaration_axioms in certificate["axioms"].values():
                assert set(declaration_axioms) <= ALLOWED
            source = ROOT / certificate["source"]
            assert digest(source) == certificate["source_sha256"]
            assert (ROOT / certificate["compiler_log"]).is_file()
            certificate_count += 1
    assert len(results) == environment["cases"] == 24
    assert certificate_count == environment["certificates"] == 48
    for name in ("RamseyCassKoopmans.lean", "lean-toolchain", "lakefile.toml",
                 "lake-manifest.json", "proof-manifest.json", "scripts/verify.py", "UNLICENSE"):
        hashes[name] = digest(ROOT / name)
    record = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "theorems": sum(counts.values()), "module_theorems": counts,
        "audited_declarations": len(declarations), "declarations": declarations,
        "full_build": "passed", "fresh_source_compilation": "passed",
        "axioms": axioms, "source_sha256": hashes,
        "fresh_audit_sha256": digest(freshpath),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "scope": config["scope"],
        "theorydebugger": {"cases": len(results), "certificates": certificate_count,
                           "saved_evidence_hashes": "passed"},
    }
    (out / "verification.json").write_text(json.dumps(record, indent=2) + "\n",
                                          encoding="utf-8", newline="\n")
    print(f"Passed build, fresh source elaboration, {len(declarations)} declaration axiom audits "
          f"({sum(counts.values())} theorems), and saved TheoryDebugger evidence checks.")


if __name__ == "__main__":
    main()
