
var x = (function (n) {
	return function (n) {
		return function fact(n) {
			if (n <= 1) return 1;
			else return n*fact(n-1);
		}
	}
})()()(4);

print(x);