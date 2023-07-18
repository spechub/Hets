import typing

import hets.haskell.Internal as Internal


class Option:
    name: str
    description: str
    typ: typing.Any
    _hs_name: str

    def __init__(self, name, description, typ, hs_name: str):
        self.name = name
        self.description = description
        self.typ = typ
        self._hs_name = hs_name

    def _hs_setter(self) -> typing.Callable[[Internal.HetcatsOpts, typing.Any], Internal.HetcatsOpts]:
        setter_name = "optsWith" + self._hs_name[0].upper() + self._hs_name[1:]
        return Internal.__dict__[setter_name]

    def _hs_getter(self) -> typing.Callable[[Internal.HetcatsOpts], typing.Any]:
        return Internal.HetcatsOpts.__dict__[self._hs_name]


_ALL_OPTIONS = [
    Option("url_catalog", "", [(str, str)], "urlCatalog"),
    Option("infiles", "", [str], "infiles"),
    Option("spec_names", "", [typing.Any], "specNames"),
    Option("trans_names", "", [typing.Any], "transNames"),
    Option("lossy_trans", "", bool, "lossyTrans"),
    Option("view_names", "", [typing.Any], "viewNames"),
    Option("libdirs", "", [str], "libdirs"),
    Option("model_spar_q", "", str, "modelSparQ"),
    Option("counter_spar_q", "", int, "counterSparQ"),
    Option("outdir", "", str, "outdir"),
    Option("database_do_migrate", "", bool, "databaseDoMigrate"),
    Option("database_output_file", "", str, "databaseOutputFile"),
    Option("database_config_file", "", str, "databaseConfigFile"),
    Option("database_sub_config_key", "", str, "databaseSubConfigKey"),
    Option("database_file_version_id", "", str, "databaseFileVersionId"),
    Option("database_reanalyze", "", bool, "databaseReanalyze"),
    Option("xupdate", "", str, "xupdate"),
    Option("recurse", "", bool, "recurse"),
    Option("verbose", "", int, "verbose"),
    Option("def_logic", "", str, "defLogic"),
    Option("def_syntax", "", str, "defSyntax"),
    Option("output_to_stdout", "", bool, "outputToStdout"),
    Option("interactive", "", bool, "interactive"),
    Option("connect_p", "", int, "connectP"),
    Option("connect_h", "", str, "connectH"),
    Option("uncolored", "", bool, "uncolored"),
    Option("xml_flag", "", bool, "xmlFlag"),
    Option("apply_automatic", "", bool, "applyAutomatic"),
    Option("compute_normal_form", "", bool, "computeNormalForm"),
    Option("dump_opts", "", [str], "dumpOpts"),
    Option("disable_certificate_verification", "", bool, "disableCertificateVerification"),
    Option("use_lib_pos", "", bool, "useLibPos"),
    Option("unlit", "", bool, "unlit"),
    Option("serve", "", bool, "serve"),
    Option("listen", "", int, "listen"),
    Option("pid_file", "", str, "pidFile"),
    Option("whitelist", "", [[str]], "whitelist"),
    Option("blacklist", "", [[str]], "blacklist"),
    Option("run_mmt", "", bool, "runMMT"),
    Option("full_theories", "", bool, "fullTheories"),
    Option("output_logic_list", "", bool, "outputLogicList"),
    Option("output_logic_graph", "", bool, "outputLogicGraph"),
    Option("file_type", "", bool, "fileType"),
    Option("access_token", "", str, "accessToken"),
    Option("http_request_headers", "", [str], "httpRequestHeaders"),
    Option("full_sign", "", bool, "fullSign"),
    Option("print_ast", "", bool, "printAST"),
]

_ALL_OPTIONS_BY_NAME = dict([(x.name, x) for x in _ALL_OPTIONS])


class Options:
    _hs_options: Internal.HetcatsOpts = None

    def __init__(self, **kwargs):
        self._hs_options = Internal.defaultHetcatsOpts

        self.patch(**kwargs)

    def __getitem__(self, key: typing.Union[str, Option]):
        if isinstance(key, Option):
            key = key.name

        if key not in _ALL_OPTIONS_BY_NAME:
            raise AttributeError(f"Unknown key '{key}'")

        option = _ALL_OPTIONS_BY_NAME[key]
        return option._hs_getter()(self._hs_options)

    def __setitem__(self, key: typing.Union[str, Option], value):
        if isinstance(key, Option):
            key = key.name

        if key not in _ALL_OPTIONS_BY_NAME:
            raise AttributeError(f"Unknown key '{key}'")

        option = _ALL_OPTIONS_BY_NAME[key]
        return option._hs_setter()(self._hs_options, value)

    def __len__(self):
        return len(_ALL_OPTIONS)

    def __iter__(self):
        return iter(_ALL_OPTIONS)

    def patch(self, **kwargs):
        for key, value in kwargs.items():
            if key in _ALL_OPTIONS_BY_NAME and value is not None:
                hs_fn = _ALL_OPTIONS_BY_NAME[key]._hs_setter()
                self._hs_options = hs_fn(self._hs_options, value)

    def to_dict(self):
        dict((option.name, option._hs_getter()(self._hs_options)) for option in _ALL_OPTIONS)


