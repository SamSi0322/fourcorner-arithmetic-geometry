"""Parse the two axiom-report formats used by the checked Lean projects."""
import re

PERMITTED = frozenset({"propext", "Classical.choice", "Quot.sound"})


def parse_axioms(text):
    entries = []
    entries.extend((name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text))
    entries.extend(re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text))
    # Native CollectAxioms audits use a tagged format, sometimes with the
    # axiom list wrapped across several lines. These are emitted only after
    # the Lean audit has also checked its complete type/value dependency cone.
    entries.extend(re.findall(r"^(?:[A-Z_]*AUDIT_AXIOMS)\s+(\S+)\s+\[([^]]*)\]", text, re.M))
    parsed = {}
    for name, raw in entries:
        axioms = {re.sub(r"\.\{[^}]*\}", "", a.strip()) for a in raw.split(",") if a.strip()}
        if not axioms <= PERMITTED:
            raise ValueError("Unexpected axiom closure: " + name + " " + repr(axioms))
        value = sorted(axioms)
        if name in parsed and parsed[name] != value:
            raise ValueError("Inconsistent axiom reports for " + name)
        parsed[name] = value
    return parsed
