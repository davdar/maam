
var x = 0;
function foo() {
	x++;
	return x;
}

while(foo() < 10) {
	if (x == 5)
		continue;
	print(x);
}

