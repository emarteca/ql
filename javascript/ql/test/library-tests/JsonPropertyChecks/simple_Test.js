let fs = require('fs'); // mark as node.js module


let input1 = '"JSON string"';

var x = JSON.parse( input1);

// expected output: the check for x sanitizes x in the body of the if
// this means, we know that x is not null, and so any accesses to properties
// of x should be fine.
if( x != undefined) {
	if(x['y']) {
		console.log("y");
	}
	if(x['z']) {
		console.log("z");
	}
}
