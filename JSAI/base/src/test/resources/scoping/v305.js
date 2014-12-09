var a = 1;

function foo() {
	bar();
	function bar() {
		print(a);
	}
	var a = 2;
	print(a);
}

foo();
print(a);

