import * as http from "http"

interface HETSApiOptions {
  readonly hostname: string;
  readonly port: number;
  readonly path: string;
}

export class Utils {

  public static queryHETSApi(_filepath: string): JSON {

    const hetsApiOptions = {
      hostname: "172.16.186.129",
      port: 8000,
      path: "/filetype/" + _filepath,
    };

    this.getJSON(hetsApiOptions).then((res: JSON) => {
      return res;
    }).catch((err: Error) => {
      console.error(err.message);
      return null;
    });

    return null;
  }

  /**
   * Executes a standard GET request but returns a promise.
   * @param _options Object containing request parameters.
   */
  private static getJSON(_options: HETSApiOptions): Promise<JSON> {
    return new Promise<JSON>((resolve, reject: (reason?: Error) => void) => {
      http.get(_options, (res) => {
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