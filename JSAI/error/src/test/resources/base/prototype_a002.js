
var foo = function() { print("constructed") };

foo["prototype"].x = 1;

var y = new foo();

var q = y instanceof foo;
print(q);


