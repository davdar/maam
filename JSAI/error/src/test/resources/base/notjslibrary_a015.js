
function f(x) {
  print("f");
  print(x);
  return x;
}

var t = 5;
var q = f(--t);   //should return 4.
print(q);


