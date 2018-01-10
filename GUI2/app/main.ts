import { app, dialog, BrowserWindow, ipcMain, Event } from "electron";
import * as path from "path";
import * as url from "url";

import { Utils } from "./utils";
import {
  QUERY_CHANNEL,
  QUERY_CHANNEL_RESPONSE,
  CONFIG_GET_CHANNEL,
  OPEN_FILE
} from "./shared/SharedConstants";

// Keep a global reference of the window object, if you don't, the window will
// be closed automatically when the JavaScript object is garbage collected.
let win: BrowserWindow = null;

function createWindow() {
  // Create the browser window.
  win = new BrowserWindow({ width: 800, height: 600 });

  // and load the index.html of the app.
  win.loadURL(
    url.format({
      pathname: path.join(__dirname, "index.html"),
      protocol: "file:",
      slashes: true
    })
  );

  // Open the DevTools.
  win.webContents.openDevTools();

  // Emitted when the window is closed.
  win.on("closed", () => {
    // Dereference the window object, usually you would store windows
    // in an array if your app supports multi windows, this is the time
    // when you should delete the corresponding element.
    win = null;
  });
}

// This method will be called when Electron has finished
// initialization and is ready to create browser windows.
// Some APIs can only be used after this event occurs.
app.on("ready", createWindow);

// Quit when all windows are closed.
app.on("window-all-closed", () => {
  // On macOS it is common for applications and their menu bar
  // to stay active until the user quits explicitly with Cmd + Q
  if (process.platform !== "darwin") {
    app.quit();
  }
});

app.on("activate", () => {
  // On macOS it's common to re-create a window in the app when the
  // dock icon is clicked and there are no other windows open.
  if (win === null) {
    createWindow();
  }
});

ipcMain.on(QUERY_CHANNEL, (event: Event, message: any) => {
  Utils.queryHETSApi(message.hostname, message.port, message.file)
    .catch((err: Error) => {
      console.error(err.message);
    })
    .then((res: JSON) => {
      event.sender.send(QUERY_CHANNEL_RESPONSE, res);
    });
});

ipcMain.on(CONFIG_GET_CHANNEL, (event: Event, _message: any) => {
  event.returnValue = Utils.getConfig();
});

ipcMain.on(OPEN_FILE, (event: Event, _message: any) => {
  dialog.showOpenDialog(
    {
      filters: [
        { name: "Hets", extensions: ["casl", "het", "hpf", "thy"] },
        { name: "All Files", extensions: ["*"] }
      ],
      properties: ["openFile"]
    },
    (paths: string[]) => {
      if (paths != undefined) {
        event.sender.send(QUERY_CHANNEL_RESPONSE, paths[0]);
      }
    }
  );
});
