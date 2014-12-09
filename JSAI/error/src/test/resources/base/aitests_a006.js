//man or boy test

function A(k, x1, x2, x3, x4, x5) { 
    print("A")
    print(k)
    function B() { print("B"); return A(--k, B, x1, x2, x3, x4); }
    if (k <= 0) {
      print("if")
      var x4_res = x4()
      print(x4_res)
      var x5_res = x5()
      print(x5_res)
      var res = x4_res + x5_res
      print(res)
      return res
    } else {
      print("else")
      var res = B();
      print(res);
      return res
    }
}
 
function K(n) {
  print("K"); print(n)
  return function() { print("anonymous"); print(n); return n }
}
 
var res = A(6, K(1), K(-1), K(-1), K(1), K(0));
print("done")
print(res)
res
