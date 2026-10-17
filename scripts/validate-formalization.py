#!/usr/bin/env python3
"""Call the unmodified, fixed official metadata contract; no Lean is run."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "vendor" / "palomar-contract"))
from scripts.submission_contract import load_formalization_metadata
from scripts.verification_errors import VerificationError


def main() -> int:
    path = ROOT / "formalization.yaml"
    try:
        data = load_formalization_metadata(path)
    except (OSError, VerificationError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    if data["project"]["license"] != "Apache-2.0":
        print("error: metadata license must match this Apache-2.0 root", file=sys.stderr)
        return 1
    print("Fixed official mechanical metadata contract accepted formalization.yaml")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
