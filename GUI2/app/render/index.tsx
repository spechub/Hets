import { remote } from "electron";
import * as React from "react";
import * as ReactDOM from "react-dom";
import "semantic-ui-css/semantic.min.css";

import { OpenUrl } from "./components/OpenUrl";
import { FDGraph } from "./components/FDGraph";
import { OpenFile } from "./components/OpenFile";
import { Grid, Container } from "semantic-ui-react";

ReactDOM.render(
  <Container fluid={true}>
    <Grid columns={1}>
      <Grid.Column>
        <Grid columns="equal" id="top">
          <Grid.Column>
            <OpenFile />
          </Grid.Column>
          <Grid.Column width={10}>
            <OpenUrl />
          </Grid.Column>
        </Grid>
      </Grid.Column>
      <Grid.Column>
        <FDGraph
          width={(
            remote.getCurrentWindow().getContentSize()[0] - 16
          ).toString()}
          height={(
            remote.getCurrentWindow().getContentSize()[1] - 150
          ).toString()}
        />
      </Grid.Column>
    </Grid>
  </Container>,
  document.getElementById("content")
);
