

function summer() {
	var sum = 0;
	for (var x = 0; x < arguments.length; ++x) {
		sum += arguments[x];
	}
	return sum;
}


var x = summer(1,2,3,4,5,6,7,8,9);
print(x);