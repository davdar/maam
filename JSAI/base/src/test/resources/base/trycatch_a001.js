var c = 0;

function f() {
  try {
    print("trying")
    //throw 5;
  }
  catch (e) {
    print("catching")
    return e;
  }
}


f(); // undef
