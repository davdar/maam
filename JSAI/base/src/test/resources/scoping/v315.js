var o = {foo: 1, bar: 2};


for (x in o) {
	print(x);
}

print(x);

for (var x in o) {
	print(x);
}

print(x);

function foo(x) {

	for (x in o) {
		print(x);
	}

	print(x);

	for (var x in o) {
		print(x);
	}

	print(x);
}

foo(20);