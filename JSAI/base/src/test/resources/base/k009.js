var x = {foo: {bar: "baz"}};
print(x.foo.bar);
var p = delete x.foo.bar;
print(p);
print(x.foo.bar);
