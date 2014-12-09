

function foo() {
  var count = 0;
  for (args in arguments) {
    print(args)
    count++;
  }
  print(count)
  return count;
}

foo(1, 2, 3);
