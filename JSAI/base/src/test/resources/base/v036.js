var p = [1,2,3];
p.push(5);
var a = p[3];

function foo() {
	try {
		switch(a) {
			case 2: ;
		}
	} catch (e) {
		throw e;
	}
}

foo();

print(a);