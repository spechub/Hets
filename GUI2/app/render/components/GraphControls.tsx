import * as React from "react";
import { Menu, Input, Checkbox } from "semantic-ui-react";

interface GraphControlProps {
  edgeStrengthsChanged: (e: any, d: any) => void;
  showInternalEdges: () => void;
  showInternalNodes: () => void;
}

export class GraphControls extends React.Component<GraphControlProps, {}> {
  constructor(props: GraphControlProps) {
    super(props);
  }

  render() {
    return (
      <Menu secondary>
        <Menu.Item>
          <Input
            type="range"
            min="0"
            max="1"
            step="any"
            onChange={this.props.edgeStrengthsChanged}
          />
        </Menu.Item>
        <Menu.Item>
          <Checkbox
            toggle
            label="Show Internal Edges"
            onChange={this.props.showInternalEdges}
          />
        </Menu.Item>
        <Menu.Item>
          <Checkbox
            toggle
            label="Hide Internal Nodes"
            onChange={this.props.showInternalNodes}
          />
        </Menu.Item>
      </Menu>
    );
  }
}
