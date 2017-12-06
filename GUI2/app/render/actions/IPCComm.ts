import { ipcRenderer, Event } from "electron";

import { QUERY_CHANNEL } from "../../shared/SharedConstants";

export class IPCComm {
  static queryHets(file: string) {
    const message = {
      file: file,
      hostname: "172.16.186.129",
      port: 8000
    };
    ipcRenderer.send(QUERY_CHANNEL, message);
  }

  static recieveMessage(
    channel: string,
    callback: (e: Event, s: string) => void
  ) {
    ipcRenderer.on(channel, callback);
  }
}
