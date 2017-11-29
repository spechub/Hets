import * as React from "react"
import { MouseEvent } from "react"

export interface OpenLogicAction {
  onClick: (event?: MouseEvent<HTMLButtonElement>) => void;
}

export class OpenLogicButton extends React.Component<OpenLogicAction, {}> {
  render() {
    return <button onClick={() => this.props.onClick() }>Open Logic</button>
  }
}