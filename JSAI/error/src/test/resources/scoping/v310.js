
function foo(x) {
	try {
		throw 5;
	} catch (x) {
		return x;
	} finally {
		throw x;
	}
}

function bar(x) {
	try {
		throw 5;
	} catch (x) {
		return x;
	} 
}

function baz(x) {
	try {
		throw 5;
	} catch (x) {
		throw x+1;
	} 
}

try {
	foo(12);
} catch (x) {
	print(x);
}

try {
	var a = bar(15);
} catch (x) {
	print("bad")
}

print(a);

try {
	baz(999);
} catch (x) {
	print(x);
}

