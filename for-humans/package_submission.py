#!/usr/bin/env python3
"""Build the TeX-only Hexagon upload, including the exact numerical checks."""

from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile


def main():
    root = Path(__file__).resolve().parent
    files = [root / "paper.tex", *sorted((root / "sections").glob("*.tex"))]
    files += [root / "anc" / name for name in (
        "check_simplification.py", "check_results.json",
        "check_finite_digits.py", "check_finite_digits.json",
        "check_controller.py", "check_controller.json",
        "check_interval_certificates.py", "check_interval_certificates.json",
        "check_packing_primitives.py", "check_packing_primitives.json",
    )]
    destination = root / "output" / "submission" / "hexagon-source.zip"
    destination.parent.mkdir(parents=True, exist_ok=True)
    with ZipFile(destination, "w", compression=ZIP_DEFLATED) as archive:
        for path in files:
            archive.write(path, path.relative_to(root))
    with ZipFile(destination) as archive:
        if archive.testzip() is not None:
            raise RuntimeError("Submission archive failed its integrity check")
        print("Submission archive:", destination)
        for name in archive.namelist():
            print(" ", name)


if __name__ == "__main__":
    main()
