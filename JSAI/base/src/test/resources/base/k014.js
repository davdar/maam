function constructor1(x, y) {
    this.x = y;
}
function constructor2(x, y) {
    this[x] = y;
}

var c1 = new constructor1("foo", "bar");
print(c1.foo);
print(c1.x);

var c2 = new constructor2("moo", "cow");
print(c2.foo);
print(c2.x);
