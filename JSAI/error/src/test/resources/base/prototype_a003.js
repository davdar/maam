
var f = function() { print("why are you in here") };
var foo = function() { print("constructed") };

foo["prototype"].x = 1;

var y = new foo();

var q = y instanceof f;
print(q);


