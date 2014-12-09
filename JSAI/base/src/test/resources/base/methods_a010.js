
var factor = 1000;

function f(x,y) {
  print(this.factor);
  print(x);
  print(y);
  return (x + y)*this.factor;
}


var arr = [2,3];
var obj = {factor:10};

var res =f.apply(this, arr);
print(res);

