factor = 7;
var res = (function f(x,y) { print(this.factor); print(x); print(y);
  return (x + y)*this.factor;}).call({factor: 10}, 2, 3);
print(res);

