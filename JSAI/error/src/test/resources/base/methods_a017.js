function sum() {
  print(arguments["0"]);
  print(arguments["1"]);
  print(arguments["2"]);
  print(arguments["3"]);
  return (arguments["0"] + arguments["1"] + arguments["2"] + arguments["3"]);
};

var res = sum(2,3,5,7);
print(res);

