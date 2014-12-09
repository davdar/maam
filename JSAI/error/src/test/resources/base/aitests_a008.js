function odd(n) {
  print("odd");
  print(n);
  if (n == 0) { print("ifodd"); return false; }
  else {
    var res = even(n - 1);
    print("elseodd");
    print(res);
    return res;
  }
}

function even(n) {
  print("even");
  print(n);
  if (n == 0) { print("ifeven"); return true; }
  else {
    var res = odd(n - 1);
    print("elseeven");
    print(res);
    return res;
  }
}

var is_17_odd = odd(17);
print("17odd");
print(is_17_odd);

