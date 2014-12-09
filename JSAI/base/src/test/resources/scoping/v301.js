
var x = function fact1(n) {
	if (n <= 1) return 1;
	else return n*fact1(n-1);
}

var y = function fact2(n) {
	if (n <= 1) return 1;
	else return n*y(n-1)
}

var a = x(4);
var b = y(4);
print(a);
print(b);