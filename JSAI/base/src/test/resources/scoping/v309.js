var x = 100;

try {
	try {
		throw 5;
	} catch (x) {
		throw x+1;
	} finally {
		throw x+2;
	}
} catch (x) {
	print(x);
}