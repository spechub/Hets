import { DGraph, DGLink, DGNode, Global, GMorphism, Axiom, Declaration, Theorem } from "../../shared/DGraph"

interface Serializable<T> {
  deserialize(input: any): T;
}

class DGLinkImpl implements DGLink, Serializable<DGLink> {
  ConsStatus?: string;
  GMorphisms: GMorphism;
  Type: string;
  id_source: number;
  id_target: number;
  linkid: number;
  source: string;
  target: string;

  deserialize(input: any): DGLink {
    this.ConsStatus = input["ConsStatus"] ? input["ConsStatus"] : null;
    this.Type = input["Type"];
    this.id_source = input["id_source"];
    this.id_target = input["id_target"];
    this.linkid = input["linkid"];
    this.source = input["source"];
    this.target = input["target"];

    return this;
  }
}

class DGNodeImpl implements DGNode, Serializable<DGNode> {
  Axioms: Axiom[];
  Declarations: Declaration[];
  Theorems: Theorem[];
  id: number;
  logic: string;
  name: string;
  range: string;
  reference: boolean;
  refname: string;
  relxpath: string;

  deserialize(input: any): DGNode {
    this.id = input["id"];
    this.logic = input["logic"];
    this.name = input["name"];
    this.range = input["range"];
    this.reference = input["reference"];
    this.refname = input["refname"];
    this.relxpath = input["relxpath"];

    return this;
  }
}

class GlobalImpl implements Global, Serializable<Global> {
  annotation: string;
  range: string;

  deserialize(input: any): Global {
    this.annotation = input["annotation"];
    this.range = input["range"];

    return this;
  }
}

class DGraphImpl implements DGraph, Serializable<DGraph> {

  DGLinks: DGLink[];
  DGNodes: DGNode[];
  Globals: Global[];
  filename: string;
  libname: string;
  dgedges: number;
  dgnodes: number;
  nextlinkid: number;

  deserialize(input: any): DGraph {
    this.filename = input["filename"];
    this.libname = input["libname"];
    this.dgedges = input["dgedges"];
    this.dgnodes = input["dgnodes"];
    this.nextlinkid = input["nextlinkid"];

    this.DGLinks = [];
    input["DGLink"].forEach((dglink: any) => {
      this.DGLinks.push(new DGLinkImpl().deserialize(dglink));
    });

    this.DGNodes = [];
    input["DGNode"].forEach((dgnode: any) => {
      this.DGNodes.push(new DGNodeImpl().deserialize(dgnode));
    });

    this.Globals = [];
    input["Global"].forEach((global: any) => {
      this.Globals.push(new GlobalImpl().deserialize(global));
    });

    return this;
  }
}

export class DGraphParser {

  public dgraph: DGraph;

  constructor(dgraph: any) {
    this.parse(dgraph);
  }

  private parse(dgraph: any) {
    this.dgraph = new DGraphImpl().deserialize(dgraph["DGraph"]);
  }
}