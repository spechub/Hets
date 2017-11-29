import * as http from "http"

interface HETSApiOptions {
  readonly hostname: string;
  readonly port: number;
  readonly path: string;
}

export class Utils {

  public static async queryHETSApi(filepath: string): Promise<JSON> {

    const hetsApiOptions = {
      hostname: "172.16.186.129",
      port: 8000,
      path: `/dg/${filepath}/?format=json`,
    };

    try {
      return await this.getJSON(hetsApiOptions);
    } catch (err) {
      throw new Error(err);
    }
  }

  /**
   * Executes a standard GET request but returns a promise.
   * @param _options Object containing request parameters.
   */
  private static getJSON(options: HETSApiOptions): Promise<JSON> {
    return new Promise<JSON>((resolve, reject: (reason?: Error) => void) => {
      http.get(options, (res) => {
        const { statusCode } = res;
        const contentType = res.headers["content-type"];

        let error: Error;
        if (statusCode !== 200) {
          error = new Error(`Request Failed. Status Code: ${statusCode}`);
        } else if (!/^application\/json/.test(contentType)) {
          error = new Error(`Invalid content-type. Expected application/json but received ${contentType}`);
        }
        if (error) {
          // consume response data to free up memory
          res.resume();
          reject(error);
        }

        res.setEncoding("utf8");
        let rawData = "";
        res.on("data", (chunk) => { rawData += chunk; });
        res.on("end", () => {
          try {
            const parsedData = JSON.parse(rawData);
            resolve(parsedData);
          } catch (err) {
            reject(err);
          }
        });
      }).on("error", (err) => {
        reject(err);
      });
    });
  }
}