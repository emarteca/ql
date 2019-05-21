let fs = require('fs'); // mark as node.js module

// this is going to be a simple test for the the JSON null checking sanitizer 
// eventually, will probably expand to be a test for the parameter checking

// also, this is inspired by the test at semmlecode-javascript-tests/library-tests/JsonParsers/tst.js

let input1 = '"JSON string"';

var x = JSON.parse( input1);

var y = x.u;

if( x.u.p) { 						// this sanitizes x.u.p
	y = x.u.p + 2; 					// x.p sanitized from condition
	y = x.u['p'] + 12;				// this is just another way of accessing x.p
	y = x.c.p; 						// x.c not sanitized
} else	
	y = x.u.p - 2; 					// x.p not sanitized here

var z = x.k.p + 16;				// x.k not yet sanitized

while( x.c.p) {					// this sanitizes x.c
	y = x.c.p + 4;				// x.c sanitized from while condition
}

let input2 = '"random string"';

x = JSON.parse( input2);

while( x.hasOwnProperty('k')) {	// this sanitizes x.k
	y = x.k.p + 6;				// x.k sanitized from condition
	y = x.w.p; 					// x.w not yet sanitized so this should be flagged
}

if ( 'z' in x) {				// this sanitizes x.z
	y = x.z.p + 3;				// x.z sanitized here from condition
} else	
	y = x.z.p - 10;				// x.z not sanitized here

let input3 = '"another string"';

x = JSON.parse( input3);

if ( x[ 'q'] != undefined) 		// this sanitizes x.q
	z = x.q.p + 12;				// so here x.q is sanitized

if( isOkOrSomething( x)) {		// this sanitizes all references to x
	y = x.l.p + 1;				// so here x.l is sanitized
}


var e; // TODO talk to max about what happens when the variables can't be resolved to strings for [] access
if( hasEOrSomething( x, e)) {	// this sanitizes all references to x
	y = x[ e].p + 1;				// so here x.e is sanitized
	y = x.l.p + 1;				// x.l not sanitized here
}

// enhanced for loop
for( const e in x) {			// our query does not select direct accesses
	y = y + x[ e].p;				// of e on x, so this should not be caught
}

assert( someFunction(x + 3, y), y); // should sanitize x forever

y = x.m + 12						// the assert sanitized x so this should not be flagged




var v = JSON.parse( '"Some random string"');
if( !v) 
	throw new Error("uh oh")

console.log( v.k)					// v is known not to be null from the previous line
console.log( v.u.k)					// v.u could be null so this should be flagged


