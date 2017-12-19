import * as React from "react";
import * as d3 from "d3";
import { Event } from "electron";

import { IPCComm } from "../actions/IPCComm";
import { DGraphParser } from "../actions/DGraphParser";
import { QUERY_CHANNEL_RESPONSE } from "../../shared/SharedConstants";

export interface FDGraphProps {
  width: string;
  height: string;
}

export class FDGraph extends React.Component<FDGraphProps, {}> {
  svg: d3.Selection<HTMLElement, any, HTMLElement, any>;
  simulation: d3.Simulation<any, any>;

  link: any;
  node: any;

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

  private renderGraph() {
    this.svg = d3.select("svg");
    const width = +this.svg.attr("width");
    const height = +this.svg.attr("height");

    this.simulation = d3
      .forceSimulation()
      .force(
        "link",
        d3.forceLink().id((d: any) => {
          return d.id;
        })
      )
      .force("charge", d3.forceManyBody())
      .force("center", d3.forceCenter(width / 2, height / 2));
  }

  private displayResp(_e: Event, s: any) {
    const graph = new DGraphParser(s);

    const links = [];
    const nodes = [];

    for (const node of graph.dgraph.DGNodes) {
      nodes.push({
        id: node.id,
        name: node.name,
        internal: node.internal
      });
    }

    for (const link of graph.dgraph.DGLinks) {
      links.push({
        id: link.linkid,
        source: link.id_source,
        target: link.id_target
      });
    }

    this.updateGraphRender(links, nodes);
  }

  private updateGraphRender(links: any, nodes: any) {
    this.link = this.svg
      .append("g")
      .attr("class", "links")
      .selectAll("line")
      .data(links)
      .enter()
      .append("line")
      .attr("stroke-width", 1);

    this.node = this.svg
      .append("g")
      .attr("class", "nodes")
      .selectAll("circle")
      .data(nodes)
      .enter()
      .append("circle")
      .attr("r", 5)
      .attr("class", (n: any) => {
        return n.internal ? "internal" : "";
      })
      .call(
        d3
          .drag()
          .on("start", this.dragstarted.bind(this))
          .on("drag", this.dragged.bind(this))
          .on("end", this.dragended.bind(this))
      );

    this.node.append("title").text((d: any) => {
      return d.name;
    });

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

    this.node
      .attr("cx", (d: any) => {
        return d.x;
      })
      .attr("cy", (d: any) => {
        return d.y;
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
