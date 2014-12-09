/* Continue test */
var flag = true;

outer:
while(flag) {
  print("outerstart")
  inner:
  print("innerlabel")
  while (true) {
    print("innerloop")
    flag = false;
    print("afterflag")
    continue outer;
    print("afterouter")
    flag = true;
  }
  print("end")
}

print(flag);
flag; // Must be false
