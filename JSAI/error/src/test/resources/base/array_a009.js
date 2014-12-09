var x = Array(6);

for (var i = 0; i < 6; i++) { 
  print("loop");
  print(i);
  x[i] = i;
}

print("three");
var x3 = x[3]; //should be 3
print(x3);


