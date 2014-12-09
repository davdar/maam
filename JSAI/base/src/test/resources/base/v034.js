
function fact(n) {
	if (n <= 0) throw "bad";
	else if (n === 1) return 1;
	else return n* fact(n-1);
}

try {
	var x = fact(5);
	print(x);
} catch (x) {
	print(x);	
}
