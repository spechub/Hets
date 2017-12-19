import * as http from "http";
import * as querystring from "querystring";
import * as fs from "fs";
import * as path from "path";
import { ConfigDesc } from "./shared/ConfigDesc";
import { CONFIG_FILENAME } from "./shared/SharedConstants";

interface HETSApiOptions {
  readonly hostname: string;
  readonly port: number;
  readonly path: string;
}

export class Utils {
  public static async queryHETSApi(
    hostname: string,
    port: number,
    filepath: string
  ): Promise<JSON> {
    const escapedFileURL = querystring.escape("file:///" + filepath);

    const hetsApiOptions = {
      hostname: hostname,
      port: port,
      path: `/dg/${escapedFileURL}/?format=json`
    };

    try {
      return await this.getJSON(hetsApiOptions);
    } catch (err) {
      throw new Error(err);
    }
  }

  public static getConfig(): ConfigDesc {
    const configStr = fs.readFileSync(
      path.join(__dirname, CONFIG_FILENAME),
      "utf8"
    );

    return JSON.parse(configStr) as ConfigDesc;
  }

  public static setConfig(config: ConfigDesc) {
    fs.writeFileSync(
      path.join(__dirname, CONFIG_FILENAME),
      JSON.stringify(config, null, 2),
      "utf8"
    );
  }

  /**
   * Executes a standard GET request but returns a promise.
   * @param _options Object containing request parameters.
   */
  private static getJSON(options: HETSApiOptions): Promise<JSON> {
    return new Promise<JSON>((resolve, reject: (reason?: Error) => void) => {
      http
        .get(options, res => {
          const { statusCode } = res;
          const contentType = res.headers["content-type"];

          let error: Error;
          if (statusCode !== 200) {
            error = new Error(`Request Failed. Status Code: ${statusCode}`);
          } else if (!/^application\/json/.test(contentType)) {
            error = new Error(
              `Invalid content-type. Expected application/json but received ${contentType}`
            );
          }
          if (error) {
            // consume response data to free up memory
            res.resume();
            reject(error);
          }

          res.setEncoding("utf8");
          let rawData = "";
          res.on("data", chunk => {
            rawData += chunk;
          });
          res.on("end", () => {
            try {
              const parsedData = JSON.parse(rawData);
              resolve(parsedData);
            } catch (err) {
              reject(err);
            }
          });
        })
        .on("error", err => {
          reject(err);
        });
    });
  }
}
