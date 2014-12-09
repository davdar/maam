
var factor = 10;

function f(x,y) {
  print(this.factor);
  print(x);
  print(y);
  return (x + y)*this.factor;
}

var obj = {factor: 1000};

var res = f.call(obj, 2, 3);
print(res);

