"""Installer integrity and repeatability tests using local synthetic archives."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import zipfile

import install_toolchain as installer
import verify_toolchain as verifier


class InstallationTests(unittest.TestCase):
    def test_unsafe_archive_paths(self):
        for path in ("/etc/passwd", "../escape", "cvc5/../../escape", "a\\b"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                installer.safe_path(path)

    def test_download_mismatch_preserves_existing_archive(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "archive.zip"
            path.write_bytes(b"existing")
            with patch.object(installer.urllib.request, "urlopen", return_value=io.BytesIO(b"wrong")):
                with self.assertRaises(ValueError):
                    installer.download(dict(url="https://example.org/archive", filename=path.name,
                                            sha256="0" * 64), path)
            self.assertEqual(path.read_bytes(), b"existing")
            self.assertEqual(list(Path(tmp).iterdir()), [path])

    def test_verified_install_and_repeat_are_identical(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            downloads = root / "downloads"
            downloads.mkdir()
            binary = "binary/bin/cvc5"
            signature = "source/proofs/eo/cpc/Cpc.eo"
            with zipfile.ZipFile(downloads / "binary.zip", "w") as archive:
                archive.writestr(binary, '#!/bin/sh\necho "cvc5 1.4.2 [git 282d5e0 on branch HEAD]"\n')
            with tarfile.open(downloads / "source.tar.gz", "w:gz") as archive:
                data = b"; synthetic signature\n"
                entry = tarfile.TarInfo(signature)
                entry.size = len(data)
                archive.addfile(entry, io.BytesIO(data))
            pins = dict(version="1.4.2", git_revision="282d5e0", install_directory="test-install",
                        binary=binary, signature=signature, archives={})
            for kind, name in (("binary", "binary.zip"), ("source", "source.tar.gz")):
                pins["archives"][kind] = dict(filename=name, url="https://example.org/unused",
                    sha256=hashlib.sha256((downloads / name).read_bytes()).hexdigest())
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps(pins))
            with patch.object(installer, "MANIFEST", manifest), patch.object(verifier, "MANIFEST", manifest):
                first = installer.install(root)
                second = installer.install(root)
                self.assertEqual(first, second)
                # Corrupt installed signatures: never overwrite or bless them.
                installed = root / "test-install" / signature
                installed.write_text("corrupt")
                with self.assertRaises(ValueError):
                    installer.install(root)
                self.assertEqual(installed.read_text(), "corrupt")


if __name__ == "__main__":
    unittest.main()
