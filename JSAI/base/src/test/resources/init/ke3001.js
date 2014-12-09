function args(){
	return arguments.length;
}

x = args(1, 2, 3);
print(x);

x = isNaN("0")
y = isNaN("zero")
print(x);
print(y);

// x = Math.max(2, 3, 4);
// y = Math.random();
// print(x);
// print(y);

x = new Number(true);
y = Number(false);
z = x.toString();
print(z);
z = y.toString(undefined);
print(z);
z = typeof x;
print(z);
z = typeof y;
print(z);


for(i in Math) print(i);

delete Math.PI;
delete Math.abs;

print(Math.hasOwnProperty("PI"));
print(Math.hasOwnProperty("abs"));

