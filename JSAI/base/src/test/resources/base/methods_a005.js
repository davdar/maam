/* Basic higher order test */

function f() {
  print("f");

  function g(x) {
    print("fg");
    print(x);
    return x*x;
  }
  return g;
}

var f_res = f()(4); // Must return 16
print(f_res);


function g(singleArgFunc) {
   print("g");
   var res = singleArgFunc(4);
   print(res);
   return res;
}

function square(x) { print("sq"); print(x); return x * x; }

g(square); // Must return 16

