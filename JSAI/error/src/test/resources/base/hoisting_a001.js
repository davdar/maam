var x = 10;

y = 5;

z = 10;

y = f();

function f() {
  print("f")
  print(y); print(x)
  var q = y-x; print(q); return q;
}


var y;
print(y);
y; // must be -5

