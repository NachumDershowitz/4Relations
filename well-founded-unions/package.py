#!/usr/bin/env python3
"""Build a deterministic source-only verification ZIP and SHA-256 checksums."""
from pathlib import Path
import argparse
import hashlib
import stat
import zipfile

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir', type=Path, default=ROOT.parent)
args = parser.parse_args()
output = args.output_dir.resolve()
if output == ROOT or output.is_relative_to(ROOT):
    raise SystemExit('The ZIP output directory must be outside the artifact directory.')
output.mkdir(parents=True, exist_ok=True)
forbidden_suffixes = {'.tex', '.pdf', '.bib', '.bbl', '.cls', '.sty', '.bst',
                      '.vo', '.vos', '.vok', '.glob', '.pyc', '.aux', '.fls',
                      '.fdb_latexmk', '.zip'}
def source_files():
    return sorted(path for path in ROOT.rglob('*') if path.is_file()
                  and path.name != '.DS_Store')


paths = source_files()
for path in paths:
    relative = path.relative_to(ROOT)
    if path.is_symlink() or path.suffix.lower() in forbidden_suffixes or any(
            part in {'.git', '.venv', 'venv', '__pycache__', '.DS_Store', 'paper', 'manuscript'}
            for part in relative.parts):
        raise SystemExit('Excluded publication material present: ' + str(relative))
manifest = ROOT / 'SHA256SUMS'
manifest.write_text(''.join(
    hashlib.sha256(path.read_bytes()).hexdigest() + '  ' + str(path.relative_to(ROOT)) + '\n'
    for path in paths if path != manifest))
paths = source_files()
archive = output / 'well-founded-unions-2026-11-09.zip'
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
    for path in paths:
        info = zipfile.ZipInfo('well-founded-unions/' + str(path.relative_to(ROOT)),
                               date_time=(2026, 11, 9, 0, 0, 0))
        info.create_system = 3
        info.external_attr = (stat.S_IFREG | (path.stat().st_mode & 0o777)) << 16
        info.compress_type = zipfile.ZIP_DEFLATED
        zipped.writestr(info, path.read_bytes(), compresslevel=9)
checksum = hashlib.sha256(archive.read_bytes()).hexdigest()
archive.with_suffix('.zip.sha256').write_text(checksum + '  ' + archive.name + '\n')
print(f'{len(paths)} files; {archive.stat().st_size} bytes; SHA-256 {checksum}')
