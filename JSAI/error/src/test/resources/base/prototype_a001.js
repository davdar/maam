
var foo = function() { print("constructed") };

foo["prototype"].x = 1;

var y = new foo();

print(y.x);

