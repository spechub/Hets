import * as React from "react";
import { Button } from "semantic-ui-react";

import { IPCComm } from "../actions/IPCComm";

export class OpenFile extends React.Component<{}, {}> {
  constructor(props: any) {
    super(props);
  }

  render() {
    return <Button onClick={() => this.openFileDialog()}>Open File</Button>;
  }

  openFileDialog() {
    IPCComm.openFileDialog();
  }
}
