
var x = 0;
function foo() {
	x++;
	return x;
}

do {
	if (x == 5)
		break;
	print(x);
} while(foo() < 10);

