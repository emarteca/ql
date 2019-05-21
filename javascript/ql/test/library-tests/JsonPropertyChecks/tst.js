let fs = require('fs'); // mark as node.js module

// this is going to be a simple test for the the JSON null checking sanitizer 
// eventually, will probably expand to be a test for the parameter checking

// also, this is inspired by the test at semmlecode-javascript-tests/library-tests/JsonParsers/tst.js

let input = '"JSON string"';

var x = JSON.parse( input);

var y = x.u;
y = x.p;

if( y) { 						// this sanitizes x.p
	y = x.p + 2; 				// x.p sanitized from condition
	y = x['p'] + 12;			// this is just another way of accessing x.p
	y = x.c; 					// x.c not sanitized
} else
	y = x.p - 2; 				// x.p not sanitized here

var z = x.k + 16;				// x.k not yet sanitized

while( x.c) {					// this sanitizes x.c
	y = x.c + 4;				// x.c sanitized from while condition
}

while( x.hasOwnProperty('k')) {	// this sanitizes x.k
	y = x.k + 6;				// x.k sanitized from condition
	y = x.w; 					// x.w not yet sanitized
}

if ( 'w' in x) {				// this sanitizes x.w
	y = x.w + 3;				// x.w sanitized here from condition
} else	
	y = x.w - 10;				// x.w not sanitized here

x.q

if ( x[ 'q'] != undefined) 		// this sanitizes x.q
	z = x.q + 12;				// so here x.q is sanitized

if( isOkOrSomething( x)) {		// this sanitizes all references to x
	y = x.l + 1;				// so here x.l is sanitized
}


var e;
if( hasEOrSomething( x, e)) {	// this sanitizes all references to x
	y = x[ e] + 1;				// so here x.e is sanitized
	y = x.l + 1;				// x.l not sanitized here
}

// enhanced for loop
for( const e in x) {			// our query does not select direct accesses
	y = y + x[ e];				// of e on x, so this should not be caught
}

assert( someFunction(x + 3, y), y); // should sanitize x forever

y = x.m + 12						// the assert sanitized x.m




var v = JSON.parse( '"Some random string"');
if( !v) 
	throw new Error("uh oh")

console.log( v.k)


