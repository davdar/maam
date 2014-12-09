
var x = function fact1(n) {
	if (n <= 1) return 1;
	else return n*fact1(n-1);
}

try {
	var y = fact1(4);
} catch (x) {
	print("caught")
}
