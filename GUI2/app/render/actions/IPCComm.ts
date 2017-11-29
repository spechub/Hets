import { ipcRenderer, Event } from "electron"

import { QUERY_CHANNEL } from "../../shared/SharedConstants"

export class IPCComm {

  static queryHets(file: string) {
    ipcRenderer.send(QUERY_CHANNEL, file);
  }

  static recieveMessage(channel: string, callback: (e: Event, s: string) => void) {
    ipcRenderer.on(channel, callback);
  }

}