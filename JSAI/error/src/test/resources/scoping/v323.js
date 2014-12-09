
var y;
var o = { 
	x: 1,
	foo: function(self) {
		y = this.x;
	}
};

o.foo();
print(y);