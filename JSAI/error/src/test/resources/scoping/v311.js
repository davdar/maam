// multiple catch blocks

try {
	throw 5;
} catch(x) {
	print(x);
}

try {
	throw 6;
} catch (x) {
	print(x);
}

try {
	throw 7;
} catch (x) {
	print(x);
}

function foo() {
	try {
		throw 51;
	} catch(x) {
		print(x);
	}

	try {
		throw 62;
	} catch (x) {
		print(x);
	}

	try {
		throw 73;
	} catch (x) {
		print(x);
	}
}

foo();