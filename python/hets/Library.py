"""
Description :  Represents `(Common.LibName.LibName, Static.DevGraph.LibEnv)`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Optional
import typing

from .HsWrapper import HsWrapper, HsHierarchyElement
from .haskell import defaultHetcatsOpts, loadLibrary as loadHsLibrary, fst, snd, getGraphForLibrary, HetcatsOpts, \
    checkConsistencyAndRecord, Result, resultToMaybe, Just, fromJust

import hets.haskell.Internal as Internal

from .DevelopmentGraph import DevelopmentGraph
from .result import result_or_raise

from .haskell import (
    automatic as automaticHs,
    globalSubsume as globalSubsumeHs,
    globalDecomposition as globalDecompositionHs,
    localInference as localInferenceHs,
    localDecomposition as localDecompositionHs,
    compositionProveEdges as compositionProveEdgesHs,
    conservativity as conservativityHs,
    automaticHideTheoremShift as automaticHideTheoremShiftHs,
    theoremHideShift as theoremHideShiftHs,
    computeColimit as computeColimitHs,
    normalForm as normalFormHs,
    triangleCons as triangleConsHs,
    freeness as freenessHs,
    libFlatImports as libFlatImportsHs,
    libFlatDUnions as libFlatDUnionsHs,
    libFlatRenamings as libFlatRenamingsHs,
    libFlatHiding as libFlatHidingHs,
    libFlatHeterogen as libFlatHeterogenHs,
    qualifyLibEnv as qualifyLibEnvHs
)


class Library(HsHierarchyElement):
    def __init__(self, hs_library) -> None:
        super().__init__(None)
        self._name = fst(hs_library)
        self._env = snd(hs_library)

        self._dgraph: Optional[DevelopmentGraph] = None

    def hs_obj(self):
        return self._name, self._env

    def hs_update(self, new_env):
        self._env = new_env

        if self._dgraph:
            hs_graph = getGraphForLibrary(self._name, self._env)
            self._dgraph.hs_update(hs_graph)

    def development_graph(self) -> DevelopmentGraph:
        if self._dgraph is None:
            self._dgraph = DevelopmentGraph(getGraphForLibrary(self._name, self._env), self)

        return self._dgraph

    def automatic(self):
        new_env = automaticHs(self._name, self._env)
        self.hs_update(new_env)

    def global_subsume(self):
        new_env = globalSubsumeHs(self._name, self._env)
        self.hs_update(new_env)

    def global_decomposition(self):
        new_env = globalDecompositionHs(self._name, self._env)
        self.hs_update(new_env)

    def local_inference(self):
        new_env = localInferenceHs(self._name, self._env)
        self.hs_update(new_env)

    def local_decomposition(self):
        new_env = localDecompositionHs(self._name, self._env)
        self.hs_update(new_env)

    def composition_prove_edges(self):
        new_env = compositionProveEdgesHs(self._name, self._env)
        self.hs_update(new_env)

    def conservativity(self):
        new_env = conservativityHs(self._name, self._env)
        self.hs_update(new_env)

    def automatic_hide_theorem_shift(self):
        new_env = automaticHideTheoremShiftHs(self._name, self._env)
        self.hs_update(new_env)

    def theorem_hide_shift(self):
        new_env_r = theoremHideShiftHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def compute_colimit(self):
        new_env_r = computeColimitHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def normal_form(self):
        new_env_r = normalFormHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def triangle_cons(self):
        new_env_r = triangleConsHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def freeness(self):
        new_env_r = freenessHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_imports(self):
        new_env_r = libFlatImportsHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_d_unions(self):
        new_env_r = libFlatDUnionsHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_renamings(self):
        new_env_r = libFlatRenamingsHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_hiding(self):
        new_env_r = libFlatHidingHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_heterogen(self):
        new_env_r = libFlatHeterogenHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def qualify_lib_env(self):
        new_env_r = qualifyLibEnvHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def hs_update_result(self, new_env_r: Result):
        new_env_m = resultToMaybe(new_env_r)
        if isinstance(new_env_m, Just):
            self.hs_update(fromJust(new_env_m))


def load_library(path: str,
                 url_catalog: Optional[typing.List[typing.Tuple[str, str]]] = None,
                 infiles: Optional[typing.List[str]] = None,
                 spec_names: Optional[typing.List[typing.Any]] = None,
                 trans_names: Optional[typing.List[typing.Any]] = None,
                 lossy_trans: Optional[bool] = None,
                 view_names: Optional[typing.List[typing.Any]] = None,
                 libdirs: Optional[typing.List[str]] = None,
                 model_spar_q: Optional[str] = None,
                 counter_spar_q: Optional[int] = None,
                 outdir: Optional[str] = None,
                 database_do_migrate: Optional[bool] = None,
                 database_output_file: Optional[str] = None,
                 database_config_file: Optional[str] = None,
                 database_sub_config_key: Optional[str] = None,
                 database_file_version_id: Optional[str] = None,
                 database_reanalyze: Optional[bool] = None,
                 xupdate: Optional[str] = None,
                 recurse: Optional[bool] = None,
                 verbose: Optional[int] = None,
                 def_logic: Optional[str] = None,
                 def_syntax: Optional[str] = None,
                 output_to_stdout: Optional[bool] = None,
                 interactive: Optional[bool] = None,
                 connect_p: Optional[int] = None,
                 connect_h: Optional[str] = None,
                 uncolored: Optional[bool] = None,
                 xml_flag: Optional[bool] = None,
                 apply_automatic: Optional[bool] = None,
                 compute_normal_form: Optional[bool] = None,
                 dump_opts: Optional[typing.List[str]] = None,
                 disable_certificate_verification: Optional[bool] = None,
                 use_lib_pos: Optional[bool] = None,
                 unlit: Optional[bool] = None,
                 serve: Optional[bool] = None,
                 listen: Optional[int] = None,
                 pid_file: Optional[str] = None,
                 whitelist: Optional[typing.List[typing.List[str]]] = None,
                 blacklist: Optional[typing.List[typing.List[str]]] = None,
                 run_mmt: Optional[bool] = None,
                 full_theories: Optional[bool] = None,
                 output_logic_list: Optional[bool] = None,
                 output_logic_graph: Optional[bool] = None,
                 file_type: Optional[bool] = None,
                 access_token: Optional[str] = None,
                 http_request_headers: Optional[typing.List[str]] = None,
                 full_sign: Optional[bool] = None,
                 print_ast: Optional[bool] = None,
                 ) -> Library:
    def get_hetcats_opts(**kwargs):
        python_names_to_haskell_fns = {
            "url_catalog": Internal.optsWithUrlCatalog,
            "infiles": Internal.optsWithInfiles,
            "spec_names": Internal.optsWithSpecNames,
            "trans_names": Internal.optsWithTransNames,
            "lossy_trans": Internal.optsWithLossyTrans,
            "view_names": Internal.optsWithViewNames,
            "libdirs": Internal.optsWithLibdirs,
            "model_spar_q": Internal.optsWithModelSparQ,
            "counter_spar_q": Internal.optsWithCounterSparQ,
            "outdir": Internal.optsWithOutdir,
            "database_do_migrate": Internal.optsWithDatabaseDoMigrate,
            "database_output_file": Internal.optsWithDatabaseOutputFile,
            "database_config_file": Internal.optsWithDatabaseConfigFile,
            "database_sub_config_key": Internal.optsWithDatabaseSubConfigKey,
            "database_file_version_id": Internal.optsWithDatabaseFileVersionId,
            "database_reanalyze": Internal.optsWithDatabaseReanalyze,
            "xupdate": Internal.optsWithXupdate,
            "recurse": Internal.optsWithRecurse,
            "verbose": Internal.optsWithVerbose,
            "def_logic": Internal.optsWithDefLogic,
            "def_syntax": Internal.optsWithDefSyntax,
            "output_to_stdout": Internal.optsWithOutputToStdout,
            "interactive": Internal.optsWithInteractive,
            "connect_p": Internal.optsWithConnectP,
            "connect_h": Internal.optsWithConnectH,
            "uncolored": Internal.optsWithUncolored,
            "xml_flag": Internal.optsWithXmlFlag,
            "apply_automatic": Internal.optsWithApplyAutomatic,
            "compute_normal_form": Internal.optsWithComputeNormalForm,
            "dump_opts": Internal.optsWithDumpOpts,
            "disable_certificate_verification": Internal.optsWithDisableCertificateVerification,
            "use_lib_pos": Internal.optsWithUseLibPos,
            "unlit": Internal.optsWithUnlit,
            "serve": Internal.optsWithServe,
            "listen": Internal.optsWithListen,
            "pid_file": Internal.optsWithPidFile,
            "whitelist": Internal.optsWithWhitelist,
            "blacklist": Internal.optsWithBlacklist,
            "run_mmt": Internal.optsWithRunMMT,
            "full_theories": Internal.optsWithFullTheories,
            "output_logic_list": Internal.optsWithOutputLogicList,
            "output_logic_graph": Internal.optsWithOutputLogicGraph,
            "file_type": Internal.optsWithFileType,
            "access_token": Internal.optsWithAccessToken,
            "http_request_headers": Internal.optsWithHttpRequestHeaders,
            "full_sign": Internal.optsWithFullSign,
            "print_ast": Internal.optsWithPrintAST,
        }

        options = defaultHetcatsOpts

        for key, value in kwargs.items():
            if key in python_names_to_haskell_fns and value is not None:
                hs_fn = python_names_to_haskell_fns[key]
                options = hs_fn(options, value)

        return options

    opts = get_hetcats_opts(
        url_catalog=url_catalog,
        infiles=infiles,
        spec_names=spec_names,
        trans_names=trans_names,
        lossy_trans=lossy_trans,
        view_names=view_names,
        libdirs=libdirs,
        model_spar_q=model_spar_q,
        counter_spar_q=counter_spar_q,
        outdir=outdir,
        database_do_migrate=database_do_migrate,
        database_output_file=database_output_file,
        database_config_file=database_config_file,
        database_sub_config_key=database_sub_config_key,
        database_file_version_id=database_file_version_id,
        database_reanalyze=database_reanalyze,
        xupdate=xupdate,
        recurse=recurse,
        verbose=verbose,
        def_logic=def_logic,
        def_syntax=def_syntax,
        output_to_stdout=output_to_stdout,
        interactive=interactive,
        connect_p=connect_p,
        connect_h=connect_h,
        uncolored=uncolored,
        xml_flag=xml_flag,
        apply_automatic=apply_automatic,
        compute_normal_form=compute_normal_form,
        dump_opts=dump_opts,
        disable_certificate_verification=disable_certificate_verification,
        use_lib_pos=use_lib_pos,
        unlit=unlit,
        serve=serve,
        listen=listen,
        pid_file=pid_file,
        whitelist=whitelist,
        blacklist=blacklist,
        run_mmt=run_mmt,
        full_theories=full_theories,
        output_logic_list=output_logic_list,
        output_logic_graph=output_logic_graph,
        file_type=file_type,
        access_token=access_token,
        http_request_headers=http_request_headers,
        full_sign=full_sign,
        print_ast=print_ast,
    )

    result = loadHsLibrary(path, opts).act()

    name_and_env = result_or_raise(result, "Failed to load library")

    return Library(name_and_env)
