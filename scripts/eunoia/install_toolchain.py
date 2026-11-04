#!/usr/bin/env python3
"""Install the pinned cvc5 binary and signatures in a private, verified cache."""
import argparse
import json
import os
import platform
from pathlib import Path, PurePosixPath
import shutil
import stat
import sys
import tarfile
import tempfile
import urllib.request
import zipfile

from verify_toolchain import MANIFEST, add_root_argument, file_sha256, verify_toolchain


def safe_path(name):
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or "\\" in name:
        raise ValueError(f"unsafe archive path: {name}")
    return path


def download(pin, path):
    if path.exists() and file_sha256(path) == pin["sha256"]:
        return
    fd, temporary = tempfile.mkstemp(prefix="download-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as target, urllib.request.urlopen(pin["url"], timeout=120) as response:
            shutil.copyfileobj(response, target)
        if file_sha256(Path(temporary)) != pin["sha256"]:
            raise ValueError(f"checksum mismatch for {pin['filename']}")
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def install(root):
    root = Path(root).expanduser()
    if not root.is_absolute():
        raise ValueError("toolchain root must be absolute")
    root = root.resolve()
    if root == Path("/") or any(root.is_relative_to(p) for p in ("/usr", "/bin", "/sbin", "/lib", "/lib64", "/etc", "/opt")):
        raise ValueError("use a private cache outside system directories")
    root.mkdir(parents=True, exist_ok=True)
    pins = json.loads(MANIFEST.read_text())
    if pins.get("platform") == "Linux-x86_64-static" and (
            platform.system() != "Linux" or platform.machine() not in ("x86_64", "amd64")):
        raise ValueError("the pinned cvc5 release requires Linux x86-64; add a verified platform pin first")
    downloads = root / "downloads"
    downloads.mkdir(exist_ok=True)
    for pin in pins["archives"].values():
        download(pin, downloads / pin["filename"])
    destination = root / pins["install_directory"]
    if destination.exists():
        # Preserve existing installations, including unexpected user files.
        return verify_toolchain(root)
    with tempfile.TemporaryDirectory(prefix="install-", dir=root) as temporary:
        stage = Path(temporary)
        with zipfile.ZipFile(downloads / pins["archives"]["binary"]["filename"]) as archive:
            for entry in archive.infolist():
                relative = safe_path(entry.filename)
                if stat.S_ISLNK(entry.external_attr >> 16):
                    raise ValueError("binary archive contains a symlink")
                target = stage / relative
                if entry.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with archive.open(entry) as src, target.open("xb") as dst:
                        shutil.copyfileobj(src, dst)
                    target.chmod(0o755 if entry.external_attr >> 16 & 0o111 else 0o644)
        # Only signature files are needed from the source tarball. Reject links.
        prefix = str(PurePosixPath(pins["signature"]).parent) + "/"
        with tarfile.open(downloads / pins["archives"]["source"]["filename"], "r:gz") as archive:
            for entry in archive:
                safe_path(entry.name)
                if not entry.name.startswith(prefix):
                    continue
                if entry.isdir():
                    continue
                if not entry.isfile():
                    raise ValueError("signature archive contains a non-regular member")
                target = stage / entry.name
                target.parent.mkdir(parents=True, exist_ok=True)
                with archive.extractfile(entry) as src, target.open("xb") as dst:
                    shutil.copyfileobj(src, dst)
        binary = stage / pins["binary"]
        binary.chmod(binary.stat().st_mode | 0o111)
        stage.rename(destination)
    return verify_toolchain(root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_root_argument(parser)
    args = parser.parse_args()
    try:
        print(json.dumps(install(args.toolchain_root), indent=2))
    except (OSError, ValueError, tarfile.TarError, zipfile.BadZipFile) as error:
        print(f"toolchain installation failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
