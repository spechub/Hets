import * as React from "react";
import { Button, Input } from "semantic-ui-react";

import { IPCComm } from "../actions/IPCComm";

export interface OpenUrlState {
  filePath: string;
}

export interface OpenUrlProps {}

export class OpenUrl extends React.Component<OpenUrlProps, OpenUrlState> {
  constructor(props: OpenUrlProps) {
    super(props);

    this.state = {
      filePath: ""
    };
  }

  render() {
    return (
      <Input
        action={<Button onClick={() => this.onClick()}>Open Url</Button>}
        type="text"
        value={this.state.filePath}
        onChange={(e, d) => this.updateFilePath(e, d)}
        fluid={true}
        placeholder="Url to file ..."
      />
    );
  }

  private updateFilePath(
    _evt: React.SyntheticEvent<HTMLInputElement>,
    data: any
  ) {
    this.setState({
      filePath: data.value
    });
  }

  private onClick() {
    console.log(this.state.filePath);
    IPCComm.queryHets(this.state.filePath);
  }
}
