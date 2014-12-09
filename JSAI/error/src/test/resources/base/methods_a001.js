
function f(x) {
  print("squaring");
  print(x);
  return x*x;
}

var g = function(x) {
  print("indirectly squaring");
  print(x);
  return f(x);
};

var fact = function factorial(x) {
  print("fact");
  print(x);

  if (x == 0) {
    print("x0");
    return 1;
  }

  else if (x==1) {  //Intentional. 
    print("x1");
    var res = x * factorial(x-1);
    print("returningx1");
    print(res);
    return res;
  }
  else {
    print("x0n1");
    var res = x * fact(x-1);
    print("returningxn0xn1");
    print(res);
    return res;
  }
};

var q = fact(g(2)); // 24
print(q);


