var x = Array(6);

for (var i = 0; i < 6;i++) { 
  print("loop");
  print(i);
  x[i] = 42;
}

print("final");
var x3 = x[3]; //should be 42
print(x3);


