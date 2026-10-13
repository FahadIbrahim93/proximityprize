#!/usr/bin/env python3
"""Clean-room audit for final proximity-prize declarations (#121).

This is a post-build audit, like scripts/axiom_audit.py. It imports the modules
listed in scripts/proximity_prize_cleanroom_targets.txt, runs `#check` and
`#print axioms` for active declarations, and fails if:

  * Lean cannot import/check the declarations,
  * any declaration depends on axioms outside
    {propext, Classical.choice, Quot.sound},
  * the signature contains residual-style hypotheses before the final
    conclusion, or
  * the expected conclusion token occurs only in a binder or arrow premise, or
  * the final conclusion token appears earlier in the signature, which catches
    goal-equivalent assumptions such as `(h : mcaPrize domain) -> mcaPrize domain`.

Pending manifest entries document future #120 prize-apex targets and are skipped
until their declarations are added.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DEFAULT_MANIFEST = Path(__file__).resolve().parent / "proximity_prize_cleanroom_targets.txt"

DEP_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NODEP_RE = re.compile(r"'([^']+)' does not depend on any axioms")

RESIDUAL_PATTERNS = [
    re.compile(r"\b[A-Za-z0-9_.']*[Rr]esidual[A-Za-z0-9_.']*\b"),
    re.compile(r"\b[A-Za-z0-9_.']*_residual[A-Za-z0-9_.']*\b"),
    re.compile(r"[\(\{\[][^)\}\]]*:\s*Prop[\)\}\]]"),
]


@dataclass(frozen=True)
class Entry:
    status: str
    module: str
    decl: str
    conclusion: str
    extra_forbidden: tuple[str, ...]
    line_no: int


def parse_manifest(path: Path) -> list[Entry]:
    entries: list[Entry] = []
    for idx, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) < 4:
            raise ValueError(f"{path}:{idx}: expected at least 4 fields")
        status, module, decl, conclusion, *extra = parts
        if status not in {"active", "pending"}:
            raise ValueError(f"{path}:{idx}: status must be active or pending")
        entries.append(
            Entry(
                status=status,
                module=module,
                decl=decl,
                conclusion=conclusion,
                extra_forbidden=tuple(extra),
                line_no=idx,
            )
        )
    return entries


def build_probe(entries: list[Entry]) -> str:
    modules = sorted({entry.module for entry in entries})
    lines = [f"import {module}" for module in modules]
    lines.extend(
        [
            "set_option pp.universes false",
            "set_option pp.all false",
            "",
        ]
    )
    for entry in entries:
        lines.append(f"#check {entry.decl}")
        lines.append(f"#print axioms {entry.decl}")
    return "\n".join(lines) + "\n"


def run_lean(src: str, timeout: int) -> tuple[int, str]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
        tf.write(src)
        tmp = Path(tf.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return proc.returncode, proc.stdout + proc.stderr
    finally:
        tmp.unlink(missing_ok=True)


def parse_axioms(output: str) -> dict[str, set[str]]:
    reported: dict[str, set[str]] = {}
    for match in DEP_RE.finditer(output):
        axioms = {item.strip() for item in match.group(2).split(",") if item.strip()}
        reported[match.group(1)] = axioms
    for match in NODEP_RE.finditer(output):
        reported[match.group(1)] = set()
    return reported


def top_level_positions(text: str, token: str) -> list[int]:
    """Locate delimiters outside printed Lean binder/type brackets."""
    closers: list[str] = []
    brackets = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
    positions: list[int] = []
    for index, char in enumerate(text):
        if char in brackets:
            closers.append(brackets[char])
        elif closers and char == closers[-1]:
            closers.pop()
        elif not closers and text.startswith(token, index):
            positions.append(index)
    return positions


def conclusion_boundary(signature: str) -> int | None:
    """Find the result after declaration binders and top-level arrow premises.

    Parenthesized result types are unwrapped before following arrows. Arrows
    inside argument types remain part of those arguments, not premise separators.
    This is a syntactic check of Lean's printed signature, not a semantic proof.
    """
    colons = top_level_positions(signature, ":")
    if not colons:
        return None
    start = colons[0] + 1
    end = len(signature)
    while True:
        while start < end and signature[start].isspace():
            start += 1
        while end > start and signature[end - 1].isspace():
            end -= 1
        result = signature[start:end]
        if result.startswith("(") and result.endswith(")"):
            # An outer pair encloses the whole type only if its first closing
            # parenthesis is at the end; `(P) → (Q)` must not be unwrapped.
            depth = 0
            for index, char in enumerate(result):
                if char == "(":
                    depth += 1
                elif char == ")":
                    depth -= 1
                    if depth == 0:
                        break
            if index == len(result) - 1:
                start += 1
                end -= 1
                continue
        arrows = top_level_positions(result, "→")
        if not arrows:
            return start
        start += arrows[-1] + 1


def token_pattern(token: str) -> re.Pattern[str]:
    """Match a conclusion identifier without accepting a longer lookalike."""
    return re.compile(rf"(?<![\w']){re.escape(token)}(?![\w'])")


def check_signature(entry: Entry, output: str) -> list[str]:
    pattern = re.compile(
        rf"(?m)^{re.escape(entry.decl)}\s*(.*?)(?=\n'[^']+' (?:depends|does not)|\Z)",
        re.S,
    )
    match = pattern.search(output)
    if not match:
        return [f"{entry.decl}: no #check signature found"]

    signature = " ".join(match.group(1).split())
    boundary = conclusion_boundary(signature)
    if boundary is None:
        return [f"{entry.decl}: no declaration result type found in #check signature"]
    conclusion_match = token_pattern(entry.conclusion).search(signature, boundary)
    if conclusion_match is None:
        return [f"{entry.decl}: conclusion token {entry.conclusion!r} not found in result type"]

    prefix = signature[:boundary]
    before_predicate = signature[:conclusion_match.start()]
    failures: list[str] = []
    if token_pattern(entry.conclusion).search(prefix):
        failures.append(
            f"{entry.decl}: conclusion token {entry.conclusion!r} appears in hypotheses"
        )

    for regex in RESIDUAL_PATTERNS:
        residual_match = regex.search(before_predicate)
        if residual_match:
            failures.append(
                f"{entry.decl}: forbidden residual/Prop hypothesis token "
                f"{residual_match.group(0)!r}"
            )

    for token in entry.extra_forbidden:
        if token in before_predicate:
            failures.append(f"{entry.decl}: forbidden manifest token {token!r} in hypotheses")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="parse the manifest and report active/pending entries without running Lean",
    )
    args = parser.parse_args()

    try:
        entries = parse_manifest(args.manifest)
    except Exception as exc:
        print(f"clean-room audit: manifest error: {exc}", file=sys.stderr)
        return 1

    active = [entry for entry in entries if entry.status == "active"]
    pending = [entry for entry in entries if entry.status == "pending"]

    if args.dry_run:
        print(f"clean-room audit manifest: {len(active)} active, {len(pending)} pending")
        for entry in active:
            print(f"ACTIVE {entry.decl} -> {entry.conclusion}")
        for entry in pending:
            print(f"PENDING {entry.decl} -> {entry.conclusion}")
        return 0

    if not active:
        print("clean-room audit: no active entries", file=sys.stderr)
        return 1

    rc, output = run_lean(build_probe(active), args.timeout)
    if rc != 0:
        print(output[:4000], file=sys.stderr)
        print("clean-room audit: Lean probe failed", file=sys.stderr)
        return 1

    reported = parse_axioms(output)
    failures: list[str] = []
    for entry in active:
        if entry.decl not in reported:
            failures.append(f"{entry.decl}: no axiom report produced")
        else:
            extra_axioms = reported[entry.decl] - ALLOWED_AXIOMS
            if extra_axioms:
                failures.append(f"{entry.decl}: forbidden axioms {sorted(extra_axioms)}")
        failures.extend(check_signature(entry, output))

    if failures:
        print("\n".join(failures), file=sys.stderr)
        print(f"\nCLEAN-ROOM AUDIT FAILED: {len(failures)} violation(s)", file=sys.stderr)
        return 1

    for entry in active:
        axioms = sorted(reported.get(entry.decl, set())) or ["<none>"]
        print(f"OK {entry.decl}: axioms={axioms}, conclusion={entry.conclusion}")
    if pending:
        print(f"clean-room audit: skipped {len(pending)} pending future target(s)")
    print(f"clean-room audit: all {len(active)} active declaration(s) clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
