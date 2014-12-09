

function f() {
  try {
    throw "trythrowed";
  }
  // // catch (v1 if v1 == 5) {
  // //   return "caughtinv1";
  // // }
  // // catch (v2 if v2 == "trythrowed") {
  // //   return "caughtinv2";
  // }
  catch (v3) {
    return "caughtinv3";
  }
}

var q = f(); // caught in v2
print(q);

