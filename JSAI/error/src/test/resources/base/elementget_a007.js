var obj = {f1: 1, f2: 2, f3: 3};

var result = "";

if ("f1" in obj) {
  print("if");
  result += "yes;";
} else {
  print("else")
  result += "no;";
}
print(result);

if (3 in obj) {
  print("if")
  result += "yes;";
} else {
  print("else")
  result += "no;";
}
print(result);

