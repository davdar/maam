/* Return stmt test cases */

var fact = function factorial(x) {
  print("fact");
  print(x);
  // XXX: this check was for x <= 0 previously--am I missing something?
  if (x > 0) {
    print("greater");
    var res = x * factorial(x-1);
    print(res);
    return res;
  } else {
    print("less");
    return 1;
  }
};

var fact_res = fact(10);  // must return 3628800
print(fact_res);

function f() {return 45; 50; 60}
var f_res = f(); // Must return 45
print(f_res);

function g() {23; 45; 60;}
var g_res = g(); // Must be undefined
print(g_res);


function h() {
  print("outerh")
  function h() {
    print("innerh")
    return "innerh"; // Must not break to outer h
  }

  h();
  print("leavingh")
  return "outerh";
}

var h_res = h();
print(h_res);

