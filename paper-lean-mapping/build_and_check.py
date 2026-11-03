#!/usr/bin/env python3
"""Build source indexes and check the paper-to-Lean and exact-check mapping.

Run from any directory with Python 3.11 or later:

    python3 -S -s -B paper-lean-mapping/build_and_check.py

The output is identical under -O. Only the standard library is used. The
script reads the TeX sources, the Lean sources, the exact checkers and the
mapping; it writes nothing. It does not compile Lean, build the PDF or run
the mathematical checks.
"""

import ast
import copy
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
MAPPING = "paper-lean-mapping/mapping.json"
BY_SECTION = "paper-lean-mapping/by-section.md"
ENVIRONMENTS = {
    "theorem": "Theorem", "proposition": "Proposition", "lemma": "Lemma",
    "corollary": "Corollary", "definition": "Definition", "remark": "Remark",
}
COVERAGES = {
    "cited": "Cited classical theorem; an input, not proved here",
    "paper_only": "Paper only",
    "paper_and_exact_checks": "Paper proof; exact checks of stated finite cases",
    "partial_lean": "Paper proof; finite ingredients proved in Lean",
}
EXACT_FOLDERS = ("verification/core/verification", "verification/core/components/verification")
TABLE_HEADER = "| Result | Label | Title | Evidence |"
TABLE_RULE = "| --- | --- | --- | --- |"
IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
QUALIFIED = r"[A-Za-z_][A-Za-z0-9_.']*"
DECLARATION = re.compile(
    r"(?:noncomputable\s+)?(def|theorem|lemma|structure|abbrev|instance|inductive|class)\s+("
    + IDENT + r")(.*)")


def need(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def reject_number(value):
    raise SystemExit("FAIL: unsupported JSON number")


def parse_json(data):
    return json.loads(data, object_pairs_hook=unique_object,
                      parse_float=reject_number, parse_constant=reject_number)


def keys(value, expected, label):
    need(isinstance(value, dict) and set(value) == set(expected), label + " fields")


def string(value, label):
    need(isinstance(value, str) and value.strip() != "", label + " text")


def strings(values, label):
    need(isinstance(values, list) and all(isinstance(x, str) for x in values), label)
    need(len(values) == len(set(values)), "duplicate " + label)
    for value in values:
        string(value, label)


def safe_path(name):
    need(isinstance(name, str) and name != "" and "\\" not in name, "source path")
    p = Path(name)
    need(not p.is_absolute() and ".." not in p.parts and p.as_posix() == name, "source path")
    return p


def relative(path):
    return path.relative_to(ROOT).as_posix()


def read_inputs():
    names = {MAPPING, BY_SECTION, "lean/TR23.lean", "lean/audit/Axioms.lean"}
    names.update(relative(p) for p in (ROOT / "paper").rglob("*.tex")
                 if not relative(p).startswith("paper/build/"))
    names.update(relative(p) for p in (ROOT / "lean" / "TR23").rglob("*.lean"))
    for folder in EXACT_FOLDERS:
        names.update(relative(p) for p in (ROOT / folder).glob("*.py"))
    result = {}
    for name in sorted(names):
        p = ROOT / safe_path(name)
        need(p.is_file() and not p.is_symlink() and p.resolve() == p,
             "missing or linked source: " + name)
        need(p.stat().st_size <= 4000000, "oversized source: " + name)
        result[name] = p.read_text(encoding="utf-8")
    return result


def tex_uncomment(line):
    for i, char in enumerate(line):
        if char == "%":
            j = i - 1
            while j >= 0 and line[j] == "\\":
                j -= 1
            if (i - j - 1) % 2 == 0:
                return line[:i]
    return line


def paper_index(sources, entry):
    """Read the section counter and the shared theorem counter in TeX order."""
    seen = set()

    def expand(name):
        safe_path(name)
        need(name.startswith("paper/") and name.endswith(".tex"), "paper input path")
        need(name in sources, "missing paper input: " + name)
        need(name not in seen, "repeated paper input: " + name)
        seen.add(name)
        output = []
        for line in sources[name].splitlines():
            line = tex_uncomment(line)
            if re.search(r"\\(?:input|include)\b", line):
                match = re.fullmatch(r"\s*\\input\{([A-Za-z0-9_/-]+)\}\s*", line)
                need(match is not None, "unsupported paper inclusion")
                output.extend(expand("paper/" + match.group(1) + ".tex"))
            else:
                output.append((name, line))
        return output

    expanded = expand(entry)
    need(seen == {n for n in sources if n.startswith("paper/") and n.endswith(".tex")},
         "unreferenced paper source")
    text = "\n".join(line for _, line in expanded)
    declarations = re.findall(r"\\newtheorem(?:\*)?[^\n]*", text)
    expected = [r"\newtheorem{theorem}{Theorem}[section]"] + [
        r"\newtheorem{" + env + "}[theorem]{" + title + "}"
        for env, title in ENVIRONMENTS.items() if env != "theorem"]
    need(declarations == expected, "unsupported theorem counter declaration")
    need(not re.search(r"\\(?:setcounter|addtocounter|counterwithin|counterwithout|appendix)\b",
                       text), "unsupported paper counter modification")
    token = re.compile(
        r"\\section(\*)?\{([^{}]+)\}|"
        r"\\(begin|end)\{([^{}]+)\}|\\label\{([^{}]+)\}")
    sections, results, labels, stack = [], [], {}, []
    section = counter = 0
    active = None
    for source, line in expanded:
        for match in token.finditer(line):
            starred, title, command, env, label = match.groups()
            if title is not None:
                need(active is None, "section inside numbered result")
                if not starred:
                    section += 1
                    counter = 0
                    sections.append({"number": section, "title": title, "source": source})
            elif command == "begin":
                stack.append(env)
                if env in ENVIRONMENTS:
                    need(active is None and section > 0, "nested or unsectioned numbered result")
                    counter += 1
                    active = {"environment": env, "number": str(section) + "." + str(counter),
                              "section": section, "source": source, "labels": [],
                              "depth": len(stack)}
                need(env.rstrip("*") not in ENVIRONMENTS or env in ENVIRONMENTS,
                     "unsupported unnumbered result environment")
            elif command == "end":
                need(stack and stack[-1] == env, "unbalanced paper environment")
                if active is not None and len(stack) == active["depth"]:
                    need(len(active["labels"]) == 1, "numbered result requires one direct label")
                    record = {k: active[k] for k in ("environment", "number", "section", "source")}
                    record["label"] = active["labels"][0]
                    results.append(record)
                    active = None
                stack.pop()
            else:
                need(label not in labels, "duplicate paper label")
                labels[label] = {"section": section, "source": source}
                if active is not None and len(stack) == active["depth"]:
                    active["labels"].append(label)
    need(not stack and active is None, "unclosed paper environment")
    return sections, results, labels


def lean_without_comments(text):
    """Mask strings and nested comments, keeping line structure."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            if text[i] == "\\":
                need(i + 1 < len(text), "unterminated Lean string")
                out.append("  ")
                i += 2
            else:
                quoted = text[i] != '"'
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        elif text[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    need(not depth and not quoted, "unterminated Lean comment or string")
    return "".join(out)


def lean_index(sources):
    """Index top-level declarations, structure fields and certificate field assignments."""
    declarations = {}
    for source in sorted(sources):
        if not source.endswith(".lean"):
            continue
        namespaces = []
        current = None
        for line in lean_without_comments(sources[source]).splitlines():
            if not line.strip():
                continue
            if line[0] not in " \t":
                current = None
                stripped = line.rstrip()
                match = re.fullmatch(r"namespace\s+(" + QUALIFIED + r")", stripped)
                if match:
                    namespaces.append(match.group(1))
                    continue
                match = re.fullmatch(r"end(?:\s+(" + QUALIFIED + r"))?", stripped)
                if match:
                    need(namespaces and match.group(1) == namespaces[-1],
                         "unsupported Lean namespace end")
                    namespaces.pop()
                    continue
                match = DECLARATION.fullmatch(stripped)
                if match:
                    kind, short, header = match.groups()
                    prefix = ".".join(namespaces)
                    name = prefix + "." + short if prefix else short
                    need(name not in declarations, "duplicate Lean declaration")
                    current = {"source": source, "kind": kind, "header": header,
                               "namespace": prefix, "fields": [], "assignments": {},
                               "instance": re.fullmatch(r"\s*:\s*(" + QUALIFIED + r")\s+where\s*",
                                                        header)}
                    declarations[name] = current
                continue
            if current is None:
                continue
            if current["kind"] == "structure":
                match = re.match(r"  (" + IDENT + r")\s*:(?!=)", line)
                if match:
                    need(match.group(1) not in current["fields"], "duplicate Lean structure field")
                    current["fields"].append(match.group(1))
            elif current["kind"] == "theorem" and current["instance"] is not None:
                match = re.match(r"  (" + IDENT + r")\s*:=\s*(\S.*?)\s*$", line)
                if match:
                    need(match.group(1) not in current["assignments"],
                         "duplicate Lean certificate field")
                    current["assignments"][match.group(1)] = match.group(2)
        need(not namespaces, "unclosed Lean namespace")
    return declarations


def resolve(declarations, namespace, identifier):
    parts = namespace.split(".") if namespace else []
    for i in range(len(parts), -1, -1):
        name = ".".join(parts[:i] + [identifier])
        if name in declarations:
            return name
    return None


def lean_structure(declarations, name, source):
    item = declarations.get(name)
    need(item is not None and item["source"] == source and item["kind"] == "structure" and
         re.fullmatch(r"\s*:\s*Prop\s+where\s*", item["header"]) is not None and
         bool(item["fields"]), "missing mapped Lean structure")
    return item


def lean_certificate(declarations, name, source, structure):
    item = declarations.get(name)
    need(item is not None and item["source"] == source and item["kind"] == "theorem",
         "missing mapped Lean theorem")
    need(item["instance"] is not None and
         resolve(declarations, item["namespace"], item["instance"].group(1)) == structure,
         "certificate theorem type")
    need(set(item["assignments"]) == set(declarations[structure]["fields"]),
         "certificate assignments differ from structure fields")
    return item


def assigned(declarations, certificate_name, certificate, field):
    value = certificate["assignments"][field]
    if re.match(r"by\b", value):
        return certificate_name
    need(re.fullmatch(QUALIFIED, value) is not None, "unsupported certificate field value")
    return resolve(declarations, certificate["namespace"], value)


def validate_lean(mapping, sources):
    declarations = lean_index(sources)
    aggregate = mapping["aggregate"]
    keys(aggregate, {"declaration", "source", "proposition", "proposition_source",
                     "axiom_probe", "scope"}, "aggregate")
    for key in aggregate:
        string(aggregate[key], "aggregate " + key)
    for path in (aggregate["source"], aggregate["proposition_source"], aggregate["axiom_probe"]):
        need(path in sources and path.endswith(".lean"), "missing Lean source")
    top = lean_structure(declarations, aggregate["proposition"], aggregate["proposition_source"])
    top_proof = lean_certificate(declarations, aggregate["declaration"], aggregate["source"],
                                 aggregate["proposition"])
    probe = lean_without_comments(sources[aggregate["axiom_probe"]])
    need(re.search(r"^#print axioms " + re.escape(aggregate["declaration"]) + r"\s*$",
                   probe, re.MULTILINE) is not None,
         "axiom probe does not name the aggregate theorem")
    owners = {aggregate["proposition"]: (top, aggregate["declaration"], top_proof)}
    composite = set()
    need(isinstance(mapping["certificates"], list), "certificates list")
    for item in mapping["certificates"]:
        keys(item, {"structure", "structure_source", "declaration", "source", "aggregate_field"},
             "certificate")
        for key in item:
            string(item[key], "certificate " + key)
        need(item["structure"] not in owners, "duplicate certificate")
        for path in (item["structure_source"], item["source"]):
            need(path in sources and path.endswith(".lean"), "missing Lean source")
        structure = lean_structure(declarations, item["structure"], item["structure_source"])
        proof = lean_certificate(declarations, item["declaration"], item["source"], item["structure"])
        field = item["aggregate_field"]
        need(field in top["fields"] and field not in composite, "aggregate certificate field")
        need(assigned(declarations, aggregate["declaration"], top_proof, field) == item["declaration"],
             "certificate field assignment mismatch")
        composite.add(field)
        owners[item["structure"]] = (structure, item["declaration"], proof)
    expected = {owner + "." + field for owner, (structure, _, _) in owners.items()
                for field in structure["fields"]
                if not (owner == aggregate["proposition"] and field in composite)}
    targets, covered = {}, set()
    need(isinstance(mapping["lean_targets"], list), "Lean targets list")
    for item in mapping["lean_targets"]:
        keys(item, {"id", "declaration", "source", "field", "scope"}, "Lean target")
        for key in item:
            string(item[key], "Lean target " + key)
        need(item["id"] not in targets, "duplicate Lean target")
        targets[item["id"]] = item
        need(item["source"] in sources and item["source"].endswith(".lean"), "missing Lean source")
        proof = declarations.get(item["declaration"])
        need(proof is not None and proof["source"] == item["source"] and proof["kind"] == "theorem",
             "missing mapped Lean theorem")
        owner, _, field = item["field"].rpartition(".")
        need(owner in owners and field in owners[owner][0]["fields"], "unknown certificate field")
        need(item["field"] in expected, "composite certificate field")
        need(item["field"] not in covered, "duplicate certificate field")
        covered.add(item["field"])
        _, certificate_name, certificate = owners[owner]
        need(assigned(declarations, certificate_name, certificate, field) == item["declaration"],
             "certificate field assignment mismatch")
    need(covered == expected, "unmapped certificate field")
    return targets, len(owners) - 1


def validate_checks(mapping, sources):
    checks = {}
    need(isinstance(mapping["exact_checks"], list), "exact checks list")
    for item in mapping["exact_checks"]:
        keys(item, {"id", "source", "function", "scope", "limitation"}, "exact check")
        for key in item:
            string(item[key], "exact check " + key)
        need(item["id"] not in checks, "duplicate exact check")
        checks[item["id"]] = item
        folder, _, name = item["source"].rpartition("/")
        need(item["source"] in sources and folder in EXACT_FOLDERS and name.endswith(".py"),
             "missing exact-check source")
        tree = ast.parse(sources[item["source"]], filename=item["source"])
        functions = [node.name for node in tree.body if isinstance(node, ast.FunctionDef)]
        need(functions.count(item["function"]) == 1, "missing mapped exact-check function")
    return checks


def table_rows(rows):
    return [TABLE_RULE] + [
        "| " + ENVIRONMENTS[row["environment"]] + " " + row["number"] + " | `" + row["label"] +
        "` | " + row["title"] + " | " + COVERAGES[row["coverage"]] + " |" for row in rows]


def validate(mapping, sources):
    keys(mapping, {"schema_version", "paper", "scope", "aggregate", "certificates",
                   "lean_targets", "exact_checks", "numbered_results", "supporting_steps"},
         "mapping")
    need(type(mapping["schema_version"]) is int and mapping["schema_version"] == 1,
         "schema version")
    need(mapping["paper"] == "paper/main.tex", "paper entry point")
    string(mapping["scope"], "mapping scope")
    sections, inventory, labels = paper_index(sources, mapping["paper"])
    targets, certificates = validate_lean(mapping, sources)
    checks = validate_checks(mapping, sources)
    used_targets, used_checks, used_labels = set(), set(), set()

    def references(row):
        need(type(row["section"]) is int and row["section"] > 0, "paper section number")
        string(row["label"], "paper label")
        string(row["source"], "paper source")
        string(row["title"], "result title")
        need("|" not in row["title"] and "`" not in row["title"], "result title characters")
        strings(row["lean_targets"], "Lean references")
        strings(row["exact_checks"], "exact-check references")
        need(set(row["lean_targets"]) <= set(targets), "unknown Lean reference")
        need(set(row["exact_checks"]) <= set(checks), "unknown exact-check reference")
        need(row["label"] in labels, "missing mapped paper label")
        need(labels[row["label"]] == {"section": row["section"], "source": row["source"]},
             "paper anchor location")
        need(row["label"] not in used_labels, "duplicate mapped paper label")
        used_labels.add(row["label"])
        used_targets.update(row["lean_targets"])
        used_checks.update(row["exact_checks"])
        string(row["covered"], "covered scope")
        string(row["paper_only"], "paper-only scope")

    rows = mapping["numbered_results"]
    need(isinstance(rows, list), "numbered results list")
    row_index = []
    for row in rows:
        keys(row, {"label", "environment", "number", "section", "source", "title", "coverage",
                   "lean_targets", "exact_checks", "covered", "paper_only"}, "numbered result")
        references(row)
        need(row["environment"] in ENVIRONMENTS, "result environment")
        string(row["number"], "result number")
        need(row["coverage"] in COVERAGES, "unsupported coverage claim")
        need((row["coverage"] == "partial_lean") == bool(row["lean_targets"]),
             "Lean coverage classification")
        need(row["coverage"] != "paper_and_exact_checks" or bool(row["exact_checks"]),
             "empty finite coverage")
        need(row["coverage"] not in ("cited", "paper_only") or not row["exact_checks"],
             "exact-check coverage classification")
        row_index.append({k: row[k] for k in ("environment", "number", "section", "source", "label")})
    need(row_index == inventory, "numbered result inventory mismatch")
    steps = mapping["supporting_steps"]
    need(isinstance(steps, list), "supporting steps list")
    for row in steps:
        keys(row, {"label", "section", "source", "title", "lean_targets", "exact_checks",
                   "covered", "paper_only"}, "supporting step")
        references(row)
        need(bool(row["lean_targets"]) or bool(row["exact_checks"]), "empty supporting step")
    need(used_targets == set(targets), "unreferenced Lean target")
    need(used_checks == set(checks), "unreferenced exact check")
    lines = sources[BY_SECTION].splitlines()
    need(lines.count(TABLE_HEADER) == 1, "section table header")
    start = lines.index(TABLE_HEADER) + 1
    block = []
    while start < len(lines) and lines[start].startswith("|"):
        block.append(lines[start])
        start += 1
    need(block == table_rows(rows), "section table mismatch")
    text = sources[BY_SECTION]
    for item in targets.values():
        need("`" + item["declaration"] + "`" in text, "Lean declaration not described in by-section.md")
    for item in checks.values():
        need("`" + item["source"] + ":" + item["function"] + "`" in text,
             "exact check not described in by-section.md")
    return (len(sections), len(inventory), len(targets), certificates, len(checks), len(steps))


def negative_controls(mapping, sources):
    cases = []

    def changed(label, mutate, expected):
        bad_mapping, bad_sources = copy.deepcopy(mapping), dict(sources)
        mutate(bad_mapping, bad_sources)
        cases.append((label, bad_mapping, bad_sources, expected))

    def edit(name, old, new, count=1):
        def mutate(m, s):
            need(old in s[name], "negative-control anchor missing: " + name)
            s[name] = s[name].replace(old, new, count)
        return mutate

    def drop(name):
        def mutate(m, s):
            need(name in s, "negative-control anchor missing: " + name)
            del s[name]
        return mutate

    rank_file = "lean/TR23/GeometryRank.lean"
    changed("missing paper label",
            lambda m, s: m["numbered_results"][0].update(label="thm:absent"),
            "missing mapped paper label")
    changed("omitted numbered result", lambda m, s: m["numbered_results"].pop(),
            "numbered result inventory mismatch")
    changed("duplicate numbered result",
            lambda m, s: m["numbered_results"].append(copy.deepcopy(m["numbered_results"][0])),
            "duplicate mapped paper label")
    changed("wrong result number",
            lambda m, s: m["numbered_results"][0].update(number="1.2"),
            "numbered result inventory mismatch")
    changed("unlabelled numbered result",
            edit("paper/main.tex", r"\end{document}", r"\begin{lemma}X\end{lemma}\end{document}"),
            "numbered result requires one direct label")
    changed("unmapped numbered result",
            edit("paper/main.tex", r"\end{document}",
                 r"\begin{lemma}\label{lem:unmapped}X\end{lemma}\end{document}"),
            "numbered result inventory mismatch")
    changed("changed theorem counter",
            edit("paper/main.tex", r"\newtheorem{theorem}{Theorem}[section]",
                 r"\newtheorem{theorem}{Theorem}"),
            "unsupported theorem counter declaration")
    changed("missing Lean theorem",
            edit(rank_file, "theorem P_kernel ", "theorem absent_kernel "),
            "missing mapped Lean theorem")
    changed("comment-only Lean theorem",
            lambda m, s: s.update({rank_file: "/- theorem P_kernel (S : Tensor3 C) : -/\n" +
                                   s[rank_file].replace("theorem P_kernel ", "theorem absent_kernel ", 1)}),
            "missing mapped Lean theorem")
    changed("missing Lean file", drop(rank_file), "missing Lean source")
    changed("wrong certificate assignment",
            lambda m, s: m["lean_targets"][4].update(declaration="TR23.Geometry.P_kernel"),
            "certificate field assignment mismatch")
    changed("unmapped certificate field", lambda m, s: m["lean_targets"].pop(),
            "unmapped certificate field")
    changed("changed certificate structure",
            edit("lean/TR23/GeometryDefinitions.lean", "  basis_image :",
                 "  extra_field : True\n  basis_image :"),
            "certificate assignments differ from structure fields")
    changed("wrong aggregate type",
            edit("lean/TR23.lean", "theorem finiteCertificate : FiniteCertificate where",
                 "theorem finiteCertificate : True where"),
            "certificate theorem type")
    changed("axiom probe", edit("lean/audit/Axioms.lean", "#print axioms TR23.finiteCertificate",
                                "#print axioms TR23.cwCertificate"),
            "axiom probe does not name the aggregate theorem")
    changed("full formalization claim",
            lambda m, s: m["numbered_results"][0].update(coverage="fully_formalized"),
            "unsupported coverage claim")
    changed("unknown Lean reference",
            lambda m, s: m["numbered_results"][0]["lean_targets"].append("absent"),
            "unknown Lean reference")
    changed("cited result with Lean target",
            lambda m, s: m["numbered_results"][1]["lean_targets"].append("threshold_lower"),
            "Lean coverage classification")
    changed("missing exact function",
            lambda m, s: m["exact_checks"][0].update(function="absent_check"),
            "missing mapped exact-check function")
    changed("missing exact-check file",
            lambda m, s: m["exact_checks"][0].update(source="verification/check_absent.py"),
            "missing exact-check source")
    changed("section table drift", edit(BY_SECTION, "| Theorem 1.1 |", "| Theorem 1.2 |"),
            "section table mismatch")
    changed("undescribed Lean declaration",
            edit(BY_SECTION, "`TR23.Geometry.P_kernel`", "`TR23.Geometry.P_kernel_absent`", -1),
            "Lean declaration not described in by-section.md")
    for label, bad_mapping, bad_sources, expected in cases:
        try:
            validate(bad_mapping, bad_sources)
        except SystemExit as error:
            need(str(error) == "FAIL: " + expected, "wrong negative-control rejection: " + label)
        else:
            raise SystemExit("FAIL: accepted negative control: " + label)
    json_cases = (('{"schema_version":1,"schema_version":1}', "duplicate JSON key"),
                  ('{"schema_version":1.0}', "unsupported JSON number"))
    for text, expected in json_cases:
        try:
            parse_json(text)
        except SystemExit as error:
            need(str(error) == "FAIL: " + expected, "wrong JSON rejection: " + expected)
        else:
            raise SystemExit("FAIL: accepted JSON control: " + expected)
    return len(cases) + len(json_cases)


def main():
    need(len(sys.argv) == 1, "this command takes no arguments")
    sources = read_inputs()
    mapping = parse_json(sources[MAPPING])
    sections, results, targets, certificates, checks, steps = validate(mapping, sources)
    controls = negative_controls(mapping, sources)
    need(read_inputs() == sources, "sources changed during check")
    print("PASS: " + str(results) + " numbered results in " + str(sections) +
          " paper sections, in TeX order")
    print("PASS: " + str(targets) + " Lean certificate fields mapped to their declarations in " +
          str(certificates) + " component certificates and TR23.finiteCertificate")
    print("PASS: " + str(checks) + " exact-check links and " + str(steps) +
          " supporting paper anchors")
    print("PASS: by-section.md result table and declaration references match the mapping")
    print("PASS: " + str(controls) + " mapping negative controls rejected")
    print("RESULT: PASS mapping structure; mathematical coverage is stated per entry")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, IndexError, AttributeError,
            SyntaxError, UnicodeError) as error:
        raise SystemExit("FAIL: mapping input: " + type(error).__name__)
