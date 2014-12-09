
obj = {f1: 2, f2: 3, f3: 5, f4: 7};

var product = 1;

for (x in obj) {
  print(x)
  var q = obj[x]
  print(q)
  product *= q
};

print(product)
product;
