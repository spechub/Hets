import * as React from "react";
import { Button, Input, Container } from "semantic-ui-react";

import { IPCComm } from "../actions/IPCComm";

export interface OpenLogicState {
  filePath: string;
}

export interface OpenLogicProps {}

export class OpenLogicButton extends React.Component<
  OpenLogicProps,
  OpenLogicState
> {
  constructor(props: OpenLogicProps) {
    super(props);

    this.state = {
      filePath: ""
    };
  }

  render() {
    return (
      <Container fluid={true}>
        <Input
          type="text"
          value={this.state.filePath}
          onChange={(e, d) => this.updateFilePath(e, d)}
        />
        <Button onClick={() => this.onClick()}>Open Logic</Button>
      </Container>
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
