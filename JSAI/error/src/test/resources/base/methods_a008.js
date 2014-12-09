
var factor = 10;

function f(x,y) {
  print(this.factor);
  print(x);
  print(y);
  return (x + y)*this.factor;
}

var obj = {factor: 10000};

var res = f.call(obj, 2);
print(res);

