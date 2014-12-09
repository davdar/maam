//man or boy test

function A(k, x1, x2, x3, x4, x5) { 
    print("A called")
    print(k)
    function B() { print("B called"); return A(--k, B, x1, x2, x3, x4); }
    return k <= 0 ? x4() + x5() : B();
}
 
function K(n) {
  print("K called")
  print(n)
  return function() { print("anonymous function called"); print(n); return n }
};
 
var res = A(6, K(1), K(-1), K(-1), K(1), K(0));
print("man or boy?")
print(res)
res
