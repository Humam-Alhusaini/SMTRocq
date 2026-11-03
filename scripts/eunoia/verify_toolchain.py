#!/usr/bin/env python3
"""Read-only, offline verification of the private cvc5 binary and CPC tree."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import zipfile


DEFAULT_ROOT = "/home/charles/code/friends/.toolchains"
MANIFEST = Path(__file__).with_name("cvc5-1.4.2.json")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def file_sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def private_root(value):
    root = Path(value).expanduser()
    if not root.is_absolute():
        raise ValueError("--toolchain-root must be an absolute private directory")
    root = root.resolve(strict=True)
    # Never fall back to PATH or accept a system installation as this toolchain.
    system_roots = ("/usr", "/bin", "/sbin", "/lib", "/lib64", "/etc", "/opt")
    if root == Path("/") or any(root.is_relative_to(p) for p in system_roots):
        raise ValueError("a private toolchain root is required, not a system directory")
    return root


def verify_toolchain(root):
    root = private_root(root)
    manifest = json.loads(MANIFEST.read_text())
    install = root / manifest["install_directory"]
    archives = {}
    for kind, pin in manifest["archives"].items():
        archive = root / "downloads" / pin["filename"]
        if file_sha256(archive) != pin["sha256"]:
            raise ValueError(f"archive checksum mismatch: {archive}")
        archives[kind] = archive

    binary = install / manifest["binary"]
    with zipfile.ZipFile(archives["binary"]) as archive:
        expected_binary = sha256(archive.read(manifest["binary"]))
    if file_sha256(binary) != expected_binary:
        raise ValueError(f"installed binary differs from pinned archive: {binary}")

    signature = install / manifest["signature"]
    prefix = str(Path(manifest["signature"]).parent) + "/"
    signatures = {}
    with tarfile.open(archives["source"], "r:gz") as archive:
        for member in archive:
            if member.isfile() and member.name.startswith(prefix):
                relative = member.name[len(prefix):]
                expected = sha256(archive.extractfile(member).read())
                if file_sha256(signature.parent / relative) != expected:
                    raise ValueError(f"signature file differs from pinned archive: {relative}")
                signatures[relative] = expected
    actual = {str(p.relative_to(signature.parent))
              for p in signature.parent.rglob("*") if p.is_file()}
    if not signatures or actual != signatures.keys():
        raise ValueError("installed CPC tree has missing or additional files")
    # Hash the entire CPC tree, including helper programs and expert signatures.
    tree_listing = "".join(f"{digest}  {name}\n"
                           for name, digest in sorted(signatures.items()))
    version = subprocess.run([str(binary), "--version"], check=True,
                             capture_output=True, text=True, timeout=10).stdout.splitlines()[0]
    expected = f"cvc5 {manifest['version']} [git {manifest['git_revision']} "
    if not version.startswith(expected):
        raise ValueError(f"unexpected solver version: {version}")
    return {
        "manifest_sha256": file_sha256(MANIFEST),
        "version": version,
        "binary": str(binary),
        "binary_sha256": expected_binary,
        "signature": str(signature),
        "signature_sha256": signatures["Cpc.eo"],
        "signature_tree_sha256": sha256(tree_listing.encode()),
        "signature_tree_files": len(signatures),
        "archives": manifest["archives"],
    }


def add_root_argument(parser):
    parser.add_argument("--toolchain-root", default=os.environ.get(
        "EUNOIA_TOOLCHAIN_ROOT", DEFAULT_ROOT), help="private root (never searched on PATH)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_root_argument(parser)
    args = parser.parse_args()
    try:
        print(json.dumps(verify_toolchain(args.toolchain_root), indent=2, sort_keys=True))
    except (OSError, ValueError, KeyError, tarfile.TarError, zipfile.BadZipFile,
            subprocess.SubprocessError) as error:
        print(f"toolchain verification failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
