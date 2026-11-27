"""Where the reference material comes from, and how to load it; and a few small helpers that the checks
share.

Everything fetched from the internet is stored under reference/downloads/, one folder per file. That
folder is not kept in Git. Each file has a recorded SHA-256 checksum, so a later download is known to be
the same file, byte for byte.

    .venv/bin/python -I reference/fetch.py        fetch whatever is missing, and verify everything

The helpers stand at the end of this file: whether a text holds a stereo mark; how many worker processes a
check starts; the argument --limit; and the lines of a script that prints PASS or FAIL for each check.
"""
import csv
import gzip
import hashlib
import io
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
DOWNLOADS = HERE / "downloads"

# name -> (file name, URL, SHA-256, what it is)
FILES = {
    "opensmiles": (
        "opensmiles.asciidoc",
        "https://raw.githubusercontent.com/opensmiles/OpenSMILES/02a7b5647e3e5bc28367ac94fc758b4d4692294d/opensmiles.asciidoc",
        "00f0423da612de913770133aa13e456d0cebc562dd50166534a8a7f9a834bd21",
        "The OpenSMILES specification, at the commit of 2026-04-02. Copyright Craig A. James, GNU Free "
        "Documentation License 1.2. It is the reference for the notation (SPEC.md, section 1).",
    ),
    "hiv": (
        "HIV.csv",
        "https://deepchemdata.s3-us-west-1.amazonaws.com/datasets/HIV.csv",
        "9ffa7fe57dc86c342627ee1d5255e937e2ab812393c73c4d16c697022f6e1d22",
        "MoleculeNet HIV: compounds of the AIDS antiviral screen of the US National Cancer Institute, as "
        "the DeepChem project hosts it. Many salts, metals and charged atoms.",
    ),
    "tox21": (
        "tox21.csv.gz",
        "https://deepchemdata.s3-us-west-1.amazonaws.com/datasets/tox21.csv.gz",
        "45d09792492ce049039dd24aa27b07fc79ce20c573187d4d90bcd178c0c0d360",
        "MoleculeNet Tox21: compounds of the Tox21 challenge of the US National Institutes of Health, as "
        "the DeepChem project hosts it. Drugs and industrial chemicals, with stereo marks.",
    ),
    "lipophilicity": (
        "Lipophilicity.csv",
        "https://deepchemdata.s3-us-west-1.amazonaws.com/datasets/Lipophilicity.csv",
        "aed41590cb30609d51d8e08ad3ff06495a76e80e211358801f596b10da69bacd",
        "MoleculeNet Lipophilicity: drug-like compounds, as the DeepChem project hosts it.",
    ),
    "bbbp": (
        "BBBP.csv",
        "https://deepchemdata.s3-us-west-1.amazonaws.com/datasets/BBBP.csv",
        "d07a38487aeac5cee5508413e468043ef3097451d2a112701c2d60be9ec6b662",
        "MoleculeNet BBBP, as the DeepChem project hosts it. Many stereo marks.",
    ),
    "clintox": (
        "clintox.csv.gz",
        "https://deepchemdata.s3-us-west-1.amazonaws.com/datasets/clintox.csv.gz",
        "7324a84a180ad9068d3847677c85d58e8432e82b3ae6ac95cf0e98b3a58d9697",
        "MoleculeNet ClinTox: drugs, as the DeepChem project hosts it. Salts, peptides, stereo marks.",
    ),
    "sider": (
        "sider.csv.gz",
        "https://deepchemdata.s3-us-west-1.amazonaws.com/datasets/sider.csv.gz",
        "4cc7ccb20dded475853c583596e227116c222c6ca7dbb40159bdbe9ee3f099b9",
        "MoleculeNet SIDER: marketed drugs, as the DeepChem project hosts it. Large molecules, stereo marks.",
    ),
}

# The data sets among the files above, in the order in which the corpus lists them.
DATA_SETS = ("hiv", "tox21", "lipophilicity", "bbbp", "clintox", "sider")

# One more data set, nci5k, needs no download: RDKit ships it.
NCI_5K_SHA256 = "91e71c015f14939837f2943dcc904f7c87e5a3a0124d82b05c28ad2f23004def"

# How many texts each data set gives when the duplicates inside a set are dropped, and how many
# different texts there are in all. A check that runs on other texts has not checked the real ones.
PER_SET = {"nci5k": 4900, "hiv": 41127, "tox21": 7831, "lipophilicity": 4200, "bbbp": 2050, "clintox": 1484,
           "sider": 1427}
DISTINCT_TEXTS = 62099


def path_of(name):
    return DOWNLOADS / name / FILES[name][0]


def sha256_of(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def checked_bytes(name):
    """The bytes of a reference file, after its checksum was compared with the recorded one. Every check
    reads the real texts through this, so no check runs on a file that is not the recorded one."""
    path, recorded = (nci_5k_path(), NCI_5K_SHA256) if name == "nci5k" else (path_of(name), FILES[name][2])
    of_rdkit = "It is a file of RDKit: install the version that reference/requirements.txt names."
    if not path.exists():
        raise SystemExit(f"THE FILE OF {name} IS MISSING: {path}\n"
                         + (of_rdkit if name == "nci5k" else "Run reference/fetch.py, which fetches it and verifies it."))
    data = path.read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != recorded:
        raise SystemExit(f"THE FILE OF {name} IS NOT THE RECORDED ONE: {path}\n  sha256   {actual}\n  recorded {recorded}\n"
                         + (of_rdkit if name == "nci5k" else
                            "Delete the file and run reference/fetch.py, which fetches it anew and verifies it."))
    return data


def nci_5k_path():
    from rdkit import RDConfig
    return Path(RDConfig.RDDataDir) / "NCI" / "first_5K.smi"


def _smiles_column(name):
    data = checked_bytes(name)
    if path_of(name).suffix == ".gz":
        data = gzip.decompress(data)
    return [row["smiles"] for row in csv.DictReader(io.StringIO(data.decode("utf-8")))]


def corpus():
    """The real SMILES texts, as a list of (data set, text). Duplicates inside a data set are dropped;
    the order is the order of the files. The texts are taken exactly as they stand in the files. Every
    file is held against its recorded checksum first, and the numbers of texts against the recorded ones."""
    sets = [("nci5k", [line.split("\t")[0] for line in checked_bytes("nci5k").decode().splitlines() if line.strip()])]
    sets += [(name, _smiles_column(name)) for name in DATA_SETS]
    out = []
    for name, texts in sets:
        seen = set()
        for t in texts:
            if t not in seen:
                seen.add(t)
                out.append((name, t))
    per_set = {name: sum(1 for n, _ in out if n == name) for name, _ in sets}
    if per_set != PER_SET or len({t for _, t in out}) != DISTINCT_TEXTS:
        raise SystemExit(f"THE REAL TEXTS ARE NOT THE RECORDED ONES: {per_set}, {len({t for _, t in out})} different texts; "
                         f"recorded: {PER_SET}, {DISTINCT_TEXTS}")
    return out


def real_texts():
    """The different real texts of all data sets together, in the order of their characters."""
    return sorted({t for _, t in corpus()})


# ------------------------------------------------------------------------ helpers that the checks share
def has_marks(text):
    """Whether the text holds one of the stereo marks `@`, `/` and `\\`."""
    return any(ch in text for ch in "@/\\")


def processor_threads():
    """How many processor threads the script may use, and how many the machine has. The first number is
    smaller where the script is fenced in (as with `taskset`)."""
    machine = os.cpu_count() or 2
    may_use = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else machine
    return may_use, machine


def workers(at_most=8):
    """How many worker processes a check starts: `at_most`, but never more than the processor threads that
    the script may use. If it may use all that the machine has, one stays free."""
    may_use, machine = processor_threads()
    return max(1, min(at_most, may_use if may_use < machine else machine - 1))


def limit_of(arguments):
    """The number behind --limit, or None if no argument is given. Any other argument ends the script: a
    mistyped option must not start the whole run."""
    if not arguments:
        return None
    if (len(arguments) == 2 and arguments[0] == "--limit" and arguments[1].isascii() and arguments[1].isdigit()
            and int(arguments[1]) > 0):
        return int(arguments[1])
    raise SystemExit(f"NOT RUN: the arguments {arguments} are not understood. Give none, or --limit and a number.")


results = []                    # for a script that prints PASS or FAIL for each check: whether each check passed


def check(what, passed, detail=""):
    """One check of such a script: a line with PASS or FAIL and what was asked, and under a FAIL the
    detail."""
    results.append(bool(passed))
    print(f"{'PASS' if passed else 'FAIL'}  {what}" + ("" if passed else f"\n        {detail}"))


def end_of_checks():
    """The last line of such a script, which counts its checks, and its exit code: 1 if a check failed."""
    print(f"\n{len(results)} checks, {results.count(False)} failed")
    return 0 if all(results) else 1
