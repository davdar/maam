function foo(x) {
  print("foo")
  print(x)
  this.a = x;
}

var p = new foo("baz");
var q = new foo("bar");

print(q.a);
q.a
