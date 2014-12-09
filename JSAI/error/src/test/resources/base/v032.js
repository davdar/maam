function double(x) {
	return 2*x;
}

function call(f, param) {
	return f(param);
}

var x = call(double, 32);

print(x);

function fmaker(f) {
	return (function() { f(); });
}

function printer() { print("hello"); }

fmaker(printer)();

function obj() {
	return {a: 1};
}

var x = obj();
var y = obj();
x.a = 1;
print(y.a);

function id(x) { return x; }

function doubler(o) {
	for (var i in o) {
		o[i] = id(o[i]);
		break;
	}
	return o;
}

var o = doubler({a: 2, b: 3, c: "6"});
print(o.c);

var arr = [1, 2];
arr.push(5);
arr.pop();
print(arr[2]);
