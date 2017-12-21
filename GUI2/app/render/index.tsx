import { remote } from "electron";
import * as React from "react";
import * as ReactDOM from "react-dom";
import "semantic-ui-css/semantic.min.css";

import { OpenLogicButton } from "./components/OpenLogic";
import { FDGraph } from "./components/FDGraph";

ReactDOM.render(
  <div>
    <OpenLogicButton />
    <FDGraph
      width={remote
        .getCurrentWindow()
        .getContentSize()[0]
        .toString()}
      height={(remote.getCurrentWindow().getContentSize()[1] - 75).toString()}
    />
  </div>,
  document.getElementById("example")
);
