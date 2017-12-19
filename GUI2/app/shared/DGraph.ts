export interface DGraph {
  DGLinks: DGLink[];
  DGNodes: DGNode[];
  Globals: Global[];
  filename: string;
  libname: string;
  dgedges: number;
  dgnodes: number;
  nextlinkid: number;
}

export interface DGLink {
  ConsStatus?: string;
  GMorphisms: GMorphism;
  Type: string;
  id_source: number;
  id_target: number;
  linkid: number;
  source: string;
  target: string;
}

export interface DGNode {
  Axioms: Axiom[];
  Declarations: Declaration[];
  Theorems: Theorem[];
  id: number;
  logic: string;
  name: string;
  range: string; // TODO: see range in Global
  reference: boolean;
  refname: string;
  relxpath: string;
  internal: boolean;
}

export interface Global {
  annotation: string;
  range: string; // TODO: actually filepath:line.char-line.char
}

export interface GMorphism {
  name: string;
}

export interface Axiom {
  Axiom: string;
  SenSymbols: SenSymbol[];
  name: string;
  range: string;
}

export interface SenSymbol {
  Symbol: string;
  iri: string;
  kind: string;
  name: string;
  range: string;
}

export interface Declaration {
  Symbol: string;
  iri: string;
  kind: string;
  name: string;
  range: string;
}

export interface Theorem {
  SenSymbols: SenSymbol[];
  Theorem: string;
  name: string;
  range: string;
  status: string;
}
