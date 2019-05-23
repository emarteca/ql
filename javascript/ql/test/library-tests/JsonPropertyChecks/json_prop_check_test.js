let fs = require('fs'); // mark as node.js module

// this is a test for all the sanitizers and the query in JSONPropExistenceWithFlow.ql
// also, this is inspired by the test at semmlecode-javascript-tests/library-tests/JsonParsers/tst.js

let input1 = '"JSON string"';

var x = JSON.parse( input1);

var y = x.u;						// flagged (x could be null)

if( x.u.p) { 						// flagged (x.u could be null)
	y = x.u.p + 2; 					// we know x.u is not null
	y = x.u['p'] + 12;				
	y = x.c.p; 						// flagged (x.c could be null)
} else	
	y = x.u.p - 2; 					// we know x.u is not null, or there would have been an error in the if check

var z = x.k.p + 16;					// flagged (x.k could be null)

while( x.c.p) {						// flagged (x.c could be null)
	y = x.c.p + 4;					
}

let input2 = '"random string"';

x = JSON.parse( input2);			// now x could be null again

while( x.hasOwnProperty('k')) {		// flagged (x could be null)
	y = x.k.p + 6;					// flagged (x.k could be null)
	y = x.w; 						
}

if ( 'o' in x.z) {					// this sanitizes x.z
	y = x.z.p + 3;					
} else	
	y = x.z.p - 10;					// flagged (x.z could be null)

let input3 = '"another string"';

x = JSON.parse( input3);			// now x could be null again

if ( x[ 'q'] != undefined) 			// this sanitizes x.q
	z = x.q.p + 12;					// we know x.q is not null

if( isOkOrSomething( x)) {			// this sanitizes x
	y = x.l + 1;					
}


var e; 
if( hasEOrSomething( x, e)) {		// this sanitizes x
	y = x[ e] + 1;				
	y = x[e].p + 1;					// flagged (x[e] could be null)
}

let input4 = '"more string"';
x = JSON.parse( input4);			// now x could be null again

// enhanced for loop
for( const e in x) {				// now we know x is not null in the loop
	y = y + x[ e];					
}

assert( someFunction(x + 3, y), y); // sanitizes x

y = x.m + 12						// the assert sanitized x so this should not be flagged




var v = JSON.parse( '"Some random string"');
if( !v) 
	throw new Error("uh oh")

console.log( v.k)					// v is known not to be null from the previous line
console.log( v.u.k)					// flagged (v.u could be null)

for ( i in v.z) {					// in the loop body we know i is a part of v.z 
	y = v.z[i]						
}

if (v.o instanceof Array) {			// instanceof sanitizes v.o
	y = v.o.b + 1					
}

console.log(v.o.k) 					// flagged (since we only knew v.o was not null in the if)

