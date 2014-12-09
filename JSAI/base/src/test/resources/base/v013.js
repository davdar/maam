var x = 1; 
var y;

function foo() {
	var x; 
	x = 123;
	return x;
}

y = foo();
print(y);