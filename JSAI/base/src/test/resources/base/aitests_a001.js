var x;
print(x)

function foo() { print("foo"); x = 1; }
function bar() { print("bar"); x = "str"; }
function blah() { print("blah"); x = true; }

function oracle() { print("oracle"); return 1 < 2; }

var func = blah;
print("funcblah")

if (oracle()) {
  func = foo;
  print("if")
} else {
  func = bar; 
  print("else")
}

func();
print(x)
x
