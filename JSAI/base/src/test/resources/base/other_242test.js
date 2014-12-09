
//From Stanford CS242 on 9/23/2012
//Passes.

var f = function() {
  var a = g();
  function g() { print("g1"); return 1; }
  function g() { print("g2"); return 2; }
  g = function() { print("g3"); return 3; }
  return a;
}

var res = f(); //should return 2
print(res);

