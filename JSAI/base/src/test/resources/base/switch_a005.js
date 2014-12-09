var i = 1;

s = "";

switch(i) {
	case 5: var s = s + "case5;"; // s must be hoisted
	case 1: s = s + "case1;";
}

print(s);
