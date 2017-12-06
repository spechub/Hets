import * as React from "react";
import * as ReactDOM from "react-dom";
import "semantic-ui-css/semantic.min.css";

import { OpenLogicButton } from "./components/OpenLogic";
import { Graph } from "./components/Graph";

ReactDOM.render(
  <div>
    <OpenLogicButton />
    <Graph />
  </div>,
  document.getElementById("example")
);
