
function g() {
  print("g");

  function f() {print("f"); return 2};

  return f() + (function (){print("a"); return 4})();
}

var res = g();
print(res);

