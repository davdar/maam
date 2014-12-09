
var obj = {
  g: function () {
    print("obj.g");
    this.k = 1;  
  },
  fact: function factorial(x) {
    print("objfact");
    print(x);
    if (x == 0) {
      print("x0");
      return 1;
    }
    else {
      print("xn0");
      var res = x * factorial(x-1);
      print("returnrecurse");
      print(res);
      return res;
    }
  }
};

 
print(obj.k);
obj.g();
print(obj.k);


var q = obj.fact(4) + obj.k;
print(q);

