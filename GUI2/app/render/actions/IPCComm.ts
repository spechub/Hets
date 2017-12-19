import { ipcRenderer, Event } from "electron";

import {
  QUERY_CHANNEL,
  CONFIG_GET_CHANNEL
} from "../../shared/SharedConstants";
import { ConfigDesc } from "../../shared/ConfigDesc";

export class IPCComm {
  public static queryHets(file: string) {
    const config = ipcRenderer.sendSync(CONFIG_GET_CHANNEL) as ConfigDesc;

    const message = {
      file: file,
      hostname: config.hets_hostname,
      port: config.hets_port
    };
    ipcRenderer.send(QUERY_CHANNEL, message);
  }

  public static recieveMessage(
    channel: string,
    callback: (e: Event, s: string) => void
  ) {
    ipcRenderer.on(channel, callback);
  }
}
