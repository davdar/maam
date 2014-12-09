function Foo(x) {
	this.x = x;
}

var o = new Foo(0);
o = new Foo("asdf");
print(o.x);