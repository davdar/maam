

function f() {
  try {
    throw "trythrew";
  }
  // catch (v1 if v1 == "something else") {
  //   return "caught in v1";
  // }
  // catch (v2 if v2 == "something totally different") {
  //   return "caught in v2";
  // }
  catch (v3) {
    return "caughtv3";
  }
}

var q = f();
print(q);

