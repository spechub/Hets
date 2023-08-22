#!/usr/bin/env node

/**
 Install markdown module:
 ------------------------
 in your home or any other directory of your choicei (e.g. /tmp/test):

	npm install --only=production --no-optional marked commander

    (when not installed in your home directory, you must be either in this
	 install directory, or add this path to your NODE_PATH env variable before
	 executing this script)

 Run:	md2html.js -h
 */

const pkg = {
	"version": "1.0.0",
	"title": "Markdown 2 html converter",
	"main": process.argv[1],
	"copyright": "(c) 2016 Jens Elkner. All rights reserved.",
	"license": "CDDL 1.0"
};

const util = require('util');
const http = require('http');
const https = require('https');
const fs = require('fs');

/** Convert data obtained from src to html using the given title as content
    for the html/head/title element and save it to fname. */
function md2html(opts, md, title, fname, src) {
	var ok = 1, s;
	var hd = '<!DOCTYPE html>\n'
		+ '<html lang="en" xml:lang="en" xmlns="http://www.w3.org/1999/xhtml">'
		+ '\n<head>\n\t<meta charset="UTF-8" />'
		+ '\t<title>' + title + '</title>\n';
	if (opts.styles != undefined && typeof opts.styles == 'string') {
		for (s of opts.styles.split(',')) {
			hd += '<link rel="stylesheet" type="text/css" href="'+ s +'"/>\n';
		}
	}
	hd += '</head>\n<body>\n';
	try {
		const marked = require('marked');
		marked.setOptions({
			gfm: true,
			tables: true,
			breaks: typeof(opts.breaks) === 'boolean' && opts.breaks,
			smartLists: true
		});
		hd += marked(md);
	} catch (e){
		console.warn('Unable to convert ' + src + ': ' + e.message);
		ok = 0;
	}
	if (ok) {
		hd += '</body></html>\n';
		if (fname === '-') {
			process.stdout.write(hd, 'utf8', function(err){});
		} else {
			fs.writeFile(fname, hd, 'utf8', function(err){});
		}
	} else if (md === undefined || md.length == 0 ) {
		hd += '<p>see <a href="' + src + '">this</a></p></pre></body></html>\n';
	} else {
		hd += '<pre>\n' + md + '\n</pre></body></html>\n';
	}
	return ok != 1;
}

function responseHandler(res) {
	var md = '';
	if (res.statusCode != 200) {
		console.error(src + ' failed with status ' + res.statusCode);
		return 1;
	}
	// console.log(`HEADERS: ${JSON.stringify(res.headers)}`);
	res.setEncoding('utf8');
	res.on('data', (chunk) => { md += chunk; });
	res.on('end', () => {
		var entry = res.req.entry;
		if (md2html(res.req.opts, md, entry[2], entry[1], entry[0]) == 0) {
			console.info(entry[1] + ' done.');
		}
		return 0;
	});
}

/**
	Parses the CLI arguments passed to this script.
	@options The property list to use to store extracted, normalized options.
	@return A list of remaining arguments aka operands.
 */
function parseCliArgs(options) {
	var cmd;
	try {
		cmd = require('commander');
	} catch (e) {
		console.error('JS module "commander" not found!\n'
			+ 'Please run "npm install --production --no-optional commander"\n'
			+ 'in your home direcrtory or adjust your NODE_PATH env variable.\n'
		);
		return 99;
	}
	if (options === undefined) {
		options = {};
	} else if (!util.isObject(options)) {
		throw new Error ('Object expected as 1st arg to parseCliArgs()!');
	}
	/* wanna have it in one place */
	options.version = pkg.version;
	options.title = pkg.title;
	options.main = pkg.main;
	cmd.version(pkg.version)
		.description(['Convert markdown into html documents.\n',
'This is a little helper to convert local or via HTTP[S] accessible markdown',
'documents into html formatted documents. It works in two modes, i.e. either',
'it gets called with the -m mapfile option (convert as many docs as given in',
'the mapfile), or to convert a single file by constructing an internal map',
'entry using the values of the options -i infile, -o outfile and -t title.',,
'Mapfile format:',
'   exports.map = [[URL, htmlfile, title],... ]',,
'  with:',
'  - URL ..      Where to fetch the markdown document. Allowed are URLs with a',
'                "http://","https://" or "file://" prefix. Everything else',
'                gets interpreted as a normal file path.',
'  - htmlfile .. The path where to store the html conversion result. One may',
'                use "-" to redirect the result to the standard output.',
'  - title ..    The string, which should be used as /html/head/title content.',
'                If unset or empty, the basename of htmlfile will be used.',,
'  Because this file gets sourced in as a JS module, one may use e.g.',
'  variables to make it more readable or even compute the "exports.map" on the',
'  fly. In this case use leading "_" to avoid var name clashes.',,
'  Example:',
"    exports.map = [",
"      [",
"        'https://raw.githubusercontent.com/nodejs/v8/master/README.md',",
"        '/tmp/index.html',",
"        'V8 JavaScript Engine'",
"      ],[",
"        'https://raw.githubusercontent.com/nodejs/doc-tool/master/README.md',",
"        '/tmp/doc-api.html',",
"        'NodeJS documentation rules'",
"      ],",
"    ]",,
'This script requires the JS modules "commander" and  "marked". To install',
'them run "npm install --only=production --no-optional commander marked" in',
'your home directory (or any other and adjust your NODE_PATH env variable).',,
'Example:',
'  ' + pkg.main + ' -t "My Page" \\',
'    -s ../styles/reset-fonts-grids-base-skin.css.gz,../styles/default.css \\',
'    -i in.md > out.html'
			].join('\n  ')
	)
	.option('-m, --map <FILE>',
		'Map file to use (options -i, -o, -t are ignored).')
	.option('-i, --in <URL>',
		'The URL of the markdown document to convert.')
	.option('-t, --title <STRING>',
		'The html page title to use.')
	.option('-o, --out <FILE>',
		'Where to store the result of the conversion.')
	.option('-b, --breaks',
		'Inline inner block level line breaks (as <br />).')
	.option('-s, --style <LIST>',
		'A comma separated CSS URL list to use in html docs.')
		/* AS IS: we explicitly allow to inject other stuff by using a properly
		   mangled string. That's a feature, not a bug. */
	;
//	 for (var i=0; i < process.argv.length; i++) {
// 		console.info(i +  " " + process.argv[i]);
// 	}
	cmd.parse(process.argv);
	options.breaks = (cmd.breaks != undefined) && cmd.breaks;
	options.styles = (cmd.style != undefined) && cmd.style;
	if (cmd.map === undefined) {
		/* construct a map from CLI args */
		if (cmd.in != undefined) {
			options.from = cmd.in
			options.to = (cmd.out != undefined) ? cmd.out : '-';
			options.title = (cmd.title != undefined) ? cmd.title : '';
			options.map = [ [ options.from, options.to, options.title ] ];
		} else {
			cmd.outputHelp();
console.dir(console);
			return 1;
		}
	} else {
		try {
			options.map = require(cmd.map).map;
		} catch (e) {
			console.error(cmd.map + ' ERROR: ' + e.message);
			return 2;
		}
		if (!Array.isArray(options.map)) {
			console.error('variable "map" is not an array (should be [][3])');
			return 3;
		}
	}
	return 0;
}

function doMain() {
	var opts = {};
	var res = parseCliArgs(opts);
	if (res)
		return res;
	var map = opts.map;
	map.forEach(function(entry, idx, array) {
		var req, md, i;

		if (!Array.isArray(entry)) {
			console.warn('map[' + idx
				+ '] is not an array (should be [3]) - skipped:\n'
				+ util.inspect(entry));
			return;
		}
		if (entry.length < 2) {
			console.warn('map[' + idx
				+ '] has one member, only (should be [3]) - skipped:\n'
				+ util.inspect(entry));
			return;
		}
		if (entry.length > 3) {
			console.warn('map[' + idx
				+ '] has more than 3 members - ignoring the overhead:\n'
				+ util.inspect(entry));
			entry = entry.slice(0,3);
		}
		if (entry.length == 2) {
			entry.push('');
		}
		// just to make sure
		entry[0] = entry[0].toString().normalize(); 
		entry[1] = entry[1].toString().normalize(); 
		if (!entry[1].match(/^[-#+-;=@-Z_a-z]+$/)) {
			console.warn('map[' + idx + '][1] (filename): '
				+ 'contains invalid characters (we allow ascii, only) - '
				+ 'skipped:\n' + util.inspect(entry));
			return;
		}
		entry[2] = entry[2].toString().normalize();
		if (entry[2].length == 0) {
			i = entry[1].lastIndexOf('/');
			entry[2] = (i == -1) ? entry[1] : entry[1].substr(i+1);
		}
		if (entry[0].startsWith('https://')) {
			req = https.request(entry[0], responseHandler);
			req.opts = opts;
		} else if (entry[0].startsWith('http://')) {
			req = http.request(entry[0], responseHandler);
			req.opts = opts;
		} else {
			// assume file
			if (entry[0].startsWith('file://')) {
				entry[0] = entry[0].substr(7);
			}
			try {
				md = fs.readFileSync(entry[0], 'utf8');
			} catch (e){
				console.warn('map[' + idx + ']: reading file ' + entry[0]
					+ 'failed: ' + e.message);
				return
			}
			if (md2html(opts, md, entry[2], entry[1], entry[0]) == 0) {
            	console.info(entry[1] + ' done.');
        	}
			return
		}
		req.entry = entry;
		req.on('error', (e) => {
			console.error('map[' + idx + '] (' + entry[0] + ') failed: '
				+ e.message);
		});
		req.end();
	});
}

console._stdout = process.stderr;
doMain();
