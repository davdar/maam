
var x = 1; 

try {
	throw 5;
} catch(x) {
	var y = x;
	print(y);
	x = 42;
	print(x);
} finally {
	print(x);
}	