var obj = {f1: {f11: 1} };

var x = obj["f1"].f11;
print(x);

var y = obj.f1["f11"];
print(y);

var z = obj["f1"]["f11"];
print(z);

var res = obj["f1"].f11 + obj.f1["f11"] + obj["f1"]["f11"];
print(res);

