let fs = require('fs'); // mark as node.js module

// this is going to be a simple test for the the JSON null checking sanitizer 
// eventually, will probably expand to be a test for the parameter checking

// also, this is inspired by the test at semmlecode-javascript-tests/library-tests/JsonParsers/tst.js

let input = '"JSON string"';

var x = JSON.parse( input);

var y;

if( x.p) { 						// this sanitizes x.p
	y = x.p + 2; 				// x.p sanitized from condition
	y = x['p'] + 12				// this is just another way of accessing x.p
	y = x.c 					// x.c not sanitized
} else
	y = x.p - 2; 				// x.p not sanitized here

var z = x.k + 16;				// x.k not yet sanitized

while( x.c) {					// this sanitizes x.c
	y = x.c + 4					// x.c sanitized from while condition
}

while( x.hasOwnProperty('k')) {	// this sanitizes x.k
	y = x.k + 6					// x.k sanitized from condition
	y = x.w 					// x.w not yet sanitized
}

if ( 'w' in x) {				// this sanitizes x.w
	y = x.w + 3					// x.w sanitized here from condition
} else	
	y = x.w - 10				// x.w not sanitized here

z = x.q

if ( x[ 'q'] != undefined) 		// this sanitizes x.q
	z = x.q + 12				// so here x.q is sanitized



