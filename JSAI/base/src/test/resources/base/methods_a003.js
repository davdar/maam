

x = (function factorial (x) {print("f"); print(x); if (x==0) return 1; return (x*factorial(x-1));})(10);
y = (function g(x) {print("g"); print(x); return x;})(3);
var z = x + y;
print(z);



