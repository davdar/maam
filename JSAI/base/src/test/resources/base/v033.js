
var o = {a: 1, b:2, c: 3};

for (var x in o) {
	if (x === "b")
		break;
}

print(x);

