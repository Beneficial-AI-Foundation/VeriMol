"""Fetch the reference files that are missing, and verify all of them against their checksums.

    .venv/bin/python -I reference/fetch.py

Prints one line per file and ends with exit code 1 if anything is missing or changed. A fetched file is
kept only if its checksum is the recorded one. A file that is there and is not the recorded one is left
as it is and reported: delete it and run this script again. A new source is added to sources.py with an
empty checksum: this script then prints the checksum to record.
"""
import hashlib
import http.client
import sys
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sources


def main():
    ok = True
    for name, (_file_name, url, expected, _what) in sources.FILES.items():
        path = sources.path_of(name)
        if not path.exists():
            request = urllib.request.Request(url, headers={"User-Agent": "python-urllib"})
            try:
                with urllib.request.urlopen(request, timeout=120) as response:
                    data = response.read()
            except (OSError, http.client.HTTPException) as problem:    # no network, no answer, or a transfer cut short
                ok = False
                print(f"BAD  not fetched {name:13s} {type(problem).__name__}: {problem}")
                continue
            actual = hashlib.sha256(data).hexdigest()
            if actual != expected:                             # compared before anything is written
                ok = False
                print(f"BAD  fetched and not kept {name:13s} {len(data):9d} bytes  sha256 {actual}"
                      f"   (recorded: {expected or 'none yet'})")
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            state = "fetched"
        else:
            state = "present"
        actual = sources.sha256_of(path)
        good = actual == expected
        ok = ok and good
        print(f"{'ok ' if good else 'BAD'}  {state:8s} {name:13s} {path.stat().st_size:9d} bytes  sha256 {actual}"
              + ("" if good else f"   (recorded: {expected or 'none yet'}; delete the file and run this script again)"))
    path = sources.nci_5k_path()
    actual = sources.sha256_of(path)
    good = actual == sources.NCI_5K_SHA256
    ok = ok and good
    print(f"{'ok ' if good else 'BAD'}  in RDKit {'nci5k':13s} {path.stat().st_size:9d} bytes  sha256 {actual}"
          + ("" if good else f"   (recorded: {sources.NCI_5K_SHA256 or 'none yet'})"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
