var obj = {i: 0};

function f() {
for (; function(){print("loop guard"); return true}();) {
  print("beginning")
  obj.i = 5;
  break;
  print("end")
}

}

f();

print(obj.i);
obj.i
