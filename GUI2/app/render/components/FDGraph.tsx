import * as React from "react";
import * as d3 from "d3";
import { Event, remote } from "electron";

import { IPCComm } from "../actions/IPCComm";
import { DGraphParser } from "../actions/DGraphParser";
import { QUERY_CHANNEL_RESPONSE } from "../../shared/SharedConstants";
import { GraphControls } from "./GraphControls";

export interface FDGraphProps {
  width: string;
  height: string;
}

interface FDGraphState {
  width: number;
  height: number;
}

export class FDGraph extends React.Component<FDGraphProps, FDGraphState> {
  svg: d3.Selection<HTMLElement, any, HTMLElement, any>;
  simulation: d3.Simulation<any, any>;
  base: d3.Selection<Element, any, HTMLElement, any>;

  graph: DGraphParser;

  link: any;
  node: any;

  internalEdges: boolean;
  internalNodes: boolean;

  constructor(props: any) {
    super(props);

    IPCComm.recieveMessage(QUERY_CHANNEL_RESPONSE, this.displayResp.bind(this));
    this.internalEdges = false;
    this.internalNodes = true;

    remote.getCurrentWindow().on("resize", () => {
      console.log("resize");
      this.setState({
        width: remote.getCurrentWindow().getContentSize()[0] - 16,
        height: remote.getCurrentWindow().getContentSize()[1] - 150
      });
    });
  }

  componentDidMount() {
    this.renderGraph();
  }

  render() {
    return (
      <>
        <svg
          width={this.state ? this.state.width : this.props.width}
          height={this.state ? this.state.height : this.props.height}
        />
        <GraphControls
          edgeStrengthsChanged={this.inputted.bind(this)}
          showInternalEdges={this.showInternalEdges.bind(this)}
          showInternalNodes={this.showInternalNodes.bind(this)}
        />
      </>
    );
  }

  private renderGraph() {
    this.svg = d3.select("svg");
    this.base = this.svg.append("g");
    const width = +this.svg.attr("width");
    const height = +this.svg.attr("height");

    this.simulation = d3
      .forceSimulation()
      .force(
        "link",
        d3
          .forceLink()
          .id((d: any) => {
            return d.id;
          })
          .strength(0.5)
      )
      .force("charge", d3.forceManyBody())
      .force("center", d3.forceCenter(width / 2, height / 2));

    this.svg.call(
      d3
        .zoom()
        .scaleExtent([1 / 2, 8])
        .on("zoom", this.zoomed.bind(this))
    );
  }

  private inputted(_e: Event, d: any) {
    (this.simulation.force("link") as any).strength(+d.value);
    this.simulation.alpha(1).restart();
  }

  private showInternalEdges() {
    this.internalEdges = !this.internalEdges;
    if (this.graph) {
      this.prepareData(this.graph);
    }
  }

  private showInternalNodes() {
    this.internalNodes = !this.internalNodes;
    if (this.graph) {
      this.prepareData(this.graph);
    }
  }

  private zoomed() {
    this.base.attr("transform", d3.event.transform);
  }

  private displayResp(_e: Event, s: any) {
    this.graph = new DGraphParser(s);
    this.prepareData(this.graph);
  }

  private prepareData(graph: DGraphParser) {
    this.base.remove();
    this.base = this.svg.append("g");
    console.log(graph);

    const links = [];
    const nodes = [];
    const excludedNodes = [];

    for (const node of graph.dgraph.DGNodes) {
      if (!this.internalNodes && node.internal) {
        excludedNodes.push(node.id);
        continue;
      }

      nodes.push({
        id: node.id,
        name: node.name,
        internal: node.internal
      });
    }

    for (const link of graph.dgraph.DGLinks) {
      if (!this.internalEdges && !link.Type.includes("GlobalDef")) {
        continue;
      }

      if (
        excludedNodes.includes(link.id_source) ||
        excludedNodes.includes(link.id_target)
      ) {
        continue;
      }

      links.push({
        id: link.linkid,
        source: link.id_source,
        target: link.id_target,
        unproven: link.Type.includes("Unproven")
      });
    }

    this.updateGraphRender(links, nodes);
  }

  private updateGraphRender(links: any, nodes: any) {
    this.link = this.base
      .append("g")
      .attr("class", "links")
      .selectAll("line")
      .data(links)
      .enter()
      .append("line")
      .attr("stroke-width", 1)
      .attr("class", (l: any) => {
        return l.unproven ? "unproven" : "";
      });

    this.node = this.base
      .append("g")
      .attr("class", "nodes")
      .selectAll("g")
      .data(nodes)
      .enter()
      .append("g")
      .call(
        d3
          .drag()
          .on("start", this.dragstarted.bind(this))
          .on("drag", this.dragged.bind(this))
          .on("end", this.dragended.bind(this))
      );

    this.node
      .append("circle")
      .attr("r", 5)
      .attr("class", (n: any) => {
        return n.internal ? "internal" : "";
      });

    this.node.append("title").text((d: any) => {
      return d.name;
    });

    this.node
      .append("text")
      .append("tspan")
      .attr("x", 7)
      .attr("y", 4)
      .text((n: any) => {
        return n.name;
      });

    this.simulation.alpha(1).restart();
    this.simulation.nodes(nodes).on("tick", this.ticked.bind(this));
    (this.simulation.force("link") as any).links(links);
  }

  private ticked() {
    this.link
      .attr("x1", (d: any) => {
        return d.source.x;
      })
      .attr("y1", (d: any) => {
        return d.source.y;
      })
      .attr("x2", (d: any) => {
        return d.target.x;
      })
      .attr("y2", (d: any) => {
        return d.target.y;
      });

    this.node.attr("transform", (n: any) => {
      return `translate(${n.x} ${n.y})`;
    });
  }

  private dragstarted(d: any) {
    if (!d3.event.active) this.simulation.alphaTarget(0.3).restart();
    d.fx = d.x;
    d.fy = d.y;
  }

  private dragged(d: any) {
    d.fx = d3.event.x;
    d.fy = d3.event.y;
  }

  private dragended(d: any) {
    if (!d3.event.active) this.simulation.alphaTarget(0);
    d.fx = null;
    d.fy = null;
  }
}
