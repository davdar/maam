var x = Array(6);

for (var i = 0;i < 6;i++) { 
  print("loop");
  print(i);
  var arr = Array(i,i+1,i+2);
  var arr_str = arr.join(",");
  print(arr_str);
  x[i] = arr;
}

print("final");
var res = x[3][2]; //should be 5
print(res);



