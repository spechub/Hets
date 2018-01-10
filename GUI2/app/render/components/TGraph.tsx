import * as React from "react";
import * as d3 from "d3";
import { Event } from "electron";

import { IPCComm } from "../actions/IPCComm";
import { DGraphParser } from "../actions/DGraphParser";
import { QUERY_CHANNEL_RESPONSE } from "../../shared/SharedConstants";

export interface TGraphProps {
  width: string;
  height: string;
}

export class TGraph extends React.Component<TGraphProps, {}> {
  svg: d3.Selection<HTMLElement, any, HTMLElement, any>;
  base: d3.Selection<Element, any, HTMLElement, any>;
  tree: any;

  constructor(props: any) {
    super(props);

    IPCComm.recieveMessage(QUERY_CHANNEL_RESPONSE, this.displayResp.bind(this));
  }

  componentDidMount() {
    this.renderGraph();
  }

  render() {
    return <svg width={this.props.width} height={this.props.height} />;
  }

  renderGraph() {
    this.svg = d3.select("svg");
    this.base = this.svg.append("g");
    const width = +this.svg.attr("width");
    const height = +this.svg.attr("height");

    this.tree = d3.tree().size([width, height]);

    this.svg.call(
      d3
        .zoom()
        .scaleExtent([1 / 2, 8])
        .on("zoom", this.zoomed.bind(this))
    );
  }

  private zoomed() {
    this.base.attr("transform", d3.event.transform);
  }

  displayResp(_e: Event, s: any) {
    this.base.remove();
    this.base = this.svg.append("g");
    const graph = new DGraphParser(s);

    console.log(graph);

    const links = [];
    const nodes = [];

    // const tree: any = {};

    for (const node of graph.dgraph.DGNodes) {
      nodes.push({
        id: node.id,
        name: node.name,
        internal: node.internal
      });
    }

    let table = [];

    let lefts: any = [];
    let rights: any = [];

    let c: number = 0;

    for (const link of graph.dgraph.DGLinks) {
      links.push({
        id: link.linkid,
        source: link.id_source,
        target: link.id_target,
        unproven: link.Type.includes("Unproven")
      });

      if (!link.Type.includes("GlobalDef")) {
        continue;
      }

      let n = nodes[link.id_target].name;
      let p = nodes[link.id_source].name;

      if (lefts.includes(n)) {
        n = n + "_" + c;
        c++;
      }

      if (rights.includes(p)) {
        p = p + "_" + c;
        c++;
      }

      table.push({
        name: n,
        parent: p
      });

      lefts.push(n);
      rights.push(p);
    }

    for (const n of rights) {
      if (!lefts.includes(n)) {
        table.push({
          name: n,
          parent: ""
        });
      }
    }

    console.log(table);

    const root = d3
      .stratify()
      .id((d: any) => {
        return d.name;
      })
      .parentId((d: any) => {
        return d.parent;
      })(table);

    console.log(root);

    this.tree(root);
    this.updateGraphRender(root);
  }

  updateGraphRender(root: any) {
    this.base
      // .append("g")
      // .attr("class", "links")
      // .selectAll("path")
      .selectAll(".link")
      .data(root.descendants().slice(1))
      .enter()
      .append("path")
      .attr("class", "link")
      .attr("d", this.diagonal.bind(this));

    const node = this.base
      // .append("g")
      // .attr("class", "nodes")
      // .selectAll("g")
      .selectAll(".node")
      .data(root.descendants())
      .enter()
      .append("g")
      .attr("transform", (d: any) => {
        return `translate(${d.y},${d.x})`;
      });

    node.append("circle").attr("r", 2.5);

    node.append("title").text((d: any) => {
      return d.id;
    });

    // node
    //   .append("text")
    //   .append("tspan")
    //   .attr("x", 7)
    //   .attr("y", 4)
    //   .text((n: any) => {
    //     return n.id;
    //   });
  }

  diagonal(d: any) {
    return (
      "M" +
      d.y +
      "," +
      d.x +
      "C" +
      (d.parent.y + 100) +
      "," +
      d.x +
      " " +
      (d.parent.y + 100) +
      "," +
      d.parent.x +
      " " +
      d.parent.y +
      "," +
      d.parent.x
    );
  }
}
