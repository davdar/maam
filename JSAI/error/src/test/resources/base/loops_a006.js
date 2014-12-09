
obj = {foo: 1, bar: 2};

fields = "";

for (x in obj) {
  print(x)
  fields += x;
};

print(fields)

