

x = (function factorial (x) {print("x's f"); print(x); if (x==0) return 1; return (x*factorial(x-1));})(10);
y = (function g(x) {print("y's g"); print(x); return x;})(3);
g = function(x) {print("g's f"); return 1;};

obj = {f1: function f(x) {print("o's 1"); print(x); return x;}, f2: function(y) {print("o's 2"); print(y); return y;}};
obj.f1(10);
obj.f2(10);

