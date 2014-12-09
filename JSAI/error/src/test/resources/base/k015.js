function constructor() {
    this.foo = "x";
    return 7;
    this.bar = "y";
}

var c = new constructor();
print(c.foo);
print(c.bar);
