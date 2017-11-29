import * as React from "react"
import { Event } from "electron"

import { IPCComm } from "../actions/IPCComm"
import { QUERY_CHANNEL_RESPONSE } from "../../shared/SharedConstants"

export interface OpenLogicState {
  filePath: string;
}

export interface OpenLogicProps {}

export class OpenLogicButton extends React.Component<OpenLogicProps, OpenLogicState> {

  constructor(props: OpenLogicProps) {
    super(props);

    this.state = {
      filePath: ""
    }

    IPCComm.recieveMessage(QUERY_CHANNEL_RESPONSE, this.displayResp)
  }

  render() {
    return (
      <div>
        <input type="text" value={ this.state.filePath } onChange={ (e) => this.updateFilePath(e) } />
        <button onClick={() => this.onClick() }>Open Logic</button>
      </div>
    );
  }

  private updateFilePath(evt: React.ChangeEvent<HTMLInputElement>) {
    this.setState({
      filePath: evt.target.value
    })
  }

  private onClick() {
    console.log(this.state.filePath);
    IPCComm.queryHets(this.state.filePath);
  }

  private displayResp(e: Event, s: string) {
    console.log(e);
    console.log(s);
  }
}