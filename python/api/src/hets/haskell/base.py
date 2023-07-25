import hyphen

if hyphen.importing and hyphen.importing.FORCED_EMPTY and hyphen.importing.EXPECTED_EMPTY:
    # Some moules in a module hierarchy do not exist in haskell. E.g. the module `Driver.Options` in python implies the existence of a module `Driver` which does not have to exist in python. Hence, these modules need to be marked explicitly empty
    hyphen.importing.FORCED_EMPTY += ["Driver", "Common", "Static", "Logic", "Proofs", "HetsAPI"]
    hyphen.importing.EXPECTED_EMPTY += ["Driver", "Common", "Static", "Logic", "Proofs", "HetsAPI"]
