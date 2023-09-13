import argparse
from io import BufferedReader, BufferedWriter
import keyword
import os
import subprocess
import re
import sys
import typing


class GHCI(object):
    def __init__(self) -> None:
        self._ghci = None

    def __enter__(self):
        self._ghci = subprocess.Popen(["make", "ghci"], stdout=subprocess.PIPE,
                                      stdin=subprocess.PIPE, stderr=subprocess.PIPE)

        # Consume initial output
        out = ""
        while not out.endswith("Prelude> "):
            buf = self._out().peek()
            self._out().read(len(buf))
            out += buf.decode("utf8")

        return self

    def __exit__(self, *args):
        self.session().terminate()
        self.session().wait()
        self._ghci = None

    def session(self) -> subprocess.Popen:
        assert self._ghci
        return self._ghci

    def _in(self) -> BufferedWriter:
        return self.session().stdin

    def _out(self) -> BufferedReader:
        return self.session().stdout

    def command(self, command: str) -> str:
        self._in().write(f"{command}\n".encode("utf8"))
        self._in().flush()

        out = ""
        while not re.search(r"^[a-zA-Z*_. ]+> $", out, re.MULTILINE):
            buf = self._out().peek()
            self._out().read(len(buf))
            out += buf.decode()

        # out = buf.decode("utf8")

        out = out[:out.rfind("\n")]
        return out


RE_TYPE = re.compile(r"^type (?:\w+\.)*(\w+) (\w+ )*= (.*)$")
RE_CONSTRUCTOR = re.compile(
    r"^(?:[A-Z]\w+\.)*([A-Z]\w+) :: (?:.* => )?((?:.*? -> )*.*?)$")
RE_FUNCTION = re.compile(
    r"^(?:[A-Z]\w+\.)*([a-z]\w+) :: (?:.* => )?((?:.*? -> )*.*?)$")
RE_CLASS = re.compile(r"^data (\w+)\s+((?:\w+ )*)= ...$")

HS_TO_PY_TYPE_MAP = {"Bool": "bool", "Int": "int", "String": "str"}


class PythonStub:
    def __init__(self, hs_module_name: str):
        self._registry = [
            (self._add_class, RE_CLASS),
            (self._add_type_alias, RE_TYPE),
            (self._add_function, RE_FUNCTION),
            (self._add_subclass, RE_CONSTRUCTOR)
        ]

        self._classes = {}
        self._types = {}
        self._functions = {}
        self._generics = {}
        self._generic_id = 0
        self._imports = []
        self._members_to_ignore = []

        self._hs_module_name = hs_module_name

    def add_haskell_declaration(self, line: str) -> None:
        found = False
        for fn, regex in self._registry:
            if regex.match(line):
                fn(line)
                found = True

        if not found:
            print(f"[E] Unknown pattern: {line}")

    def add_import(self, module: str) -> None:
        self._imports += [module]

    def ignore_members(self, members_to_ignore: typing.List[str]):
        self._members_to_ignore = members_to_ignore

    def to_pyi(self) -> str:
        return "\n".join([
            f'""" Auto generated python stubs for haskell module {self._hs_module_name or ""}"""',
            "",
            "import typing",
            "",
            *[f'from {module} import *' for module in self._imports],
            "",
            *[f'{n} = typing.TypeVar("{n}")  # {orig}' for orig,
              n in self._generics.items()],
            "",
            *self._types.values(),
            "",
            *self._classes.values(),
            "",
            *self._functions.values(),
            ""
        ])

    def to_py(self) -> str:
        return "\n".join([
            f'""" Auto generated python imports for haskell module {self._hs_module_name}"""',
            "",
            "from .base import *",
            "",
            f"from hs.{self._hs_module_name} import (",
            "    # type imports",
            *[f"    {n}," for n in self._types.keys()],
            "",
            "    # class imports",
            *[f"    {n}," for n in self._classes.keys()],
            "",
            "    # function imports",
            *[f"    {n}," for n in self._functions.keys()],
            ")",
            ""
        ])

    def _member_ok(self, name: str, context: str) -> bool:
        if keyword.iskeyword(name):
            print(
                f"[E] {context} name is a reservered keyword in python '{name}'")
            return False

        if name in self._members_to_ignore:
            return False

        return True

    def _generic_var(self, orig: str | None = None) -> str:
        if orig in self._generics:
            return self._generics[orig]

        name = f"G_{self._generic_id}"

        if orig is None:
            orig = name.lower()

        self._generics[orig] = name
        self._generic_id += 1
        return name

    def _parse_parens(self, term: str, delimiter: str) -> typing.List[str]:
        parts = []
        parens = 0
        part = ""
        i = 0
        while i < len(term):
            c = term[i]
            if c == '(':
                parens += 1
            elif c == ')':
                parens -= 1

            if i < len(term) - len(delimiter) and term[i:i+len(delimiter)] == delimiter and parens == 0:
                parts += [part.strip()]
                part = ""
                i += len(delimiter)
                continue
            else:
                part += c

            i += 1

        parts += [part.strip()]
        return parts

    def _parse_tuple(self, term: str) -> typing.List[str] | None:
        if len(term) < 2 or term[0] != "(" or term[-1] != ")":
            return None

        return self._parse_parens(term[1:-1], ",")

    def _parse_function(self, term: str) -> typing.List[str]:
        return self._parse_parens(term, "->")

    def _add_class(self, line: str):
        match = RE_CLASS.match(line)

        class_name = match.group(1)
        params = match.group(2)

        if not self._member_ok(class_name, "class"):
            return

        if params is not None and params != "":
            params = params.strip().split(" ")

            gen_params = [self._generic_var(p.strip()) for p in params]

            self._classes[class_name] = f"class {class_name}(typing.Generic[{', '.join(gen_params)}]): ..."
        else:
            self._classes[class_name] = f"class {class_name}: ..."

        return self._classes[class_name]

    def _add_subclass(self, line: str):
        def sub_fn(match: re.Match[str]) -> str:
            groups = match.groups()
            out = f"class {groups[0]}"

            params = self._parse_function(groups[1])

            assert params is not None

            params = [self._to_type(p) for p in params]

            if params[-1] != groups[0]:
                out += f"({params[-1]})"

            out += ":"

            if len(params) > 1:
                out += "\n    def __init__(self, "

                for i, param in enumerate(params[:-1]):
                    if i > 0:
                        out += ", "
                    out += f"x{i}: {param}"

                out += "): ..."
            else:
                out += " ..."

            return out

        class_name = RE_CONSTRUCTOR.match(line).group(1)

        if not self._member_ok(class_name, "class"):
            return

        self._classes[class_name] = RE_CONSTRUCTOR.sub(sub_fn, line)

    def _add_type_alias(self, line: str):

        match = RE_TYPE.match(line)
        type_name = match.group(1)
        definition = match.group(3)

        if not self._member_ok(type_name, "type alias"):
            return

        definition_type = self._to_type(definition)

        self._types[type_name] = f"{type_name} = {definition_type}"

    def _add_function(self, line: str):
        def sub_fn(match: re.Match[str]) -> str:
            groups = match.groups()
            out = f"def {groups[0]}("

            params = self._parse_function(groups[1])

            assert params is not None

            params = [self._to_type(p) for p in params]

            for i, param in enumerate(params[:-1]):
                if i > 0:
                    out += ", "
                out += f"x{i}: {param}"

            out += f") -> {params[-1]}: ..."

            return out

        fn_name = RE_FUNCTION.match(line).group(1)

        if not self._member_ok(fn_name, "function"):
            return

        self._functions[fn_name] = RE_FUNCTION.sub(sub_fn, line)

    def _to_type(self, term: str) -> str:
        assert term != ""
                
        if parts := self._parse_tuple(term):
            if len(parts) == 1:
                return self._to_type(parts[0])

            nested = [self._to_type(p) for p in parts]
            return f"typing.Tuple[{', '.join(nested)}]"

        if term[0] == "[" and term[-1] == "]":
            nested = self._to_type(term[1:-1].strip())
            return f"typing.List[{nested}]"

        parts = self._parse_function(term)
        if len(parts) >= 2:
            param_types = [self._to_type(p.strip()) for p in parts[1:]]
            ret_type = self._to_type(parts[0])

            return f"typing.Callable[[{', '.join(param_types)}], {ret_type}]"

        if " " in term:
            parts = self._parse_parens(term, " ")

            assert len(parts) >= 2

            typ = self._to_type(parts[0])
            type_args = [self._to_type(p) for p in parts[1:]]
            return f"{typ}[{','.join(type_args)}]"

        if term in HS_TO_PY_TYPE_MAP:
            return HS_TO_PY_TYPE_MAP[term]

        if term[0].islower():
            name = self._generic_var(term)
            return name

        return term.split(".")[-1]


def main():
    parser = argparse.ArgumentParser()
    config_group = parser.add_mutually_exclusive_group(required=True)

    manual_config = config_group.add_argument_group()
    manual_config.add_argument("modulenames", nargs="*")
    manual_config.add_argument(
        "-i", "--import", dest="modules_to_import", nargs="*")

    config_group.add_argument(
        "-c", "--config", type=argparse.FileType("r"), nargs="?")

    parser.add_argument("-o", "--output-directory",
                        default=os.getcwd(), nargs="?")

    args = parser.parse_args()

    if args.config:
        import json
        config = json.load(args.config)
    else:
        config = [{
            "name": m,
            "imports": args.modules_to_import}
            for m in args.modulenames]

    print("Generating stubs for modules: " +
          ", ".join(c["name"] for c in config))

    with GHCI() as ghci:
        for i, module in enumerate(config):
            print(f"Module {module['name']}:")
            print("  loading ...", end="")
            try:
                ghci.command(f":l {module['name']}")
            except Exception as e:
                print(" failed")
                raise e
            print(" done")

            print("  generating stubs ...", end="")
            try:
                content = ghci.command(f":browse! {module['name']}")

                text = re.sub(r"\n\s+", " ", content, flags=re.MULTILINE)
                lines = text.splitlines()
                lines = [line.strip()
                         for line in lines if not line.strip().startswith("--")]

                stub = PythonStub(module["name"])
                stub.ignore_members(module.get("ignore", []))
                for line in lines:
                    if line.strip() == "":
                        continue
                    stub.add_haskell_declaration(line)

                for import_module in module.get("imports", []):
                    stub.add_import(import_module)

                filename = os.path.join(
                    args.output_directory, module['name'].split(".")[-1])

                with open(f"{filename}.pyi", "w") as f:
                    f.write(stub.to_pyi())

                with open(f"{filename}.py", "w") as f:
                    f.write(stub.to_py())

            except Exception as e:
                print(" failed")
                raise e
            print(" done")


if __name__ == "__main__":
    main()
