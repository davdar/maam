var obj = {
  fact: function (x) {
    print("fact");
    print(x);
    if (x != 0) {
      print("xn0");
      var res = x*this.factorial(x-1);
      print("factrecur")
      print(res);
      return res;
    } else {
      print("xn0");
      return 1;
    }
  },

  factorial: function (x) {
    print("factorial");
    print(x);
    if (x != 0) {
      print("xn0")
      var res = x * this.fact(x-1);
      print("factorialrecur");
      print(res);
      return res;
    } else {
      print("xis0")
      return 1;
    }
  }
};


obj.fact(4);

