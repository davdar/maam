var true1 = Boolean(true)
var true1_ty = typeof(true1)
print(true1_ty)
var true1_val = true1.valueOf()
print(true1_val)

var true2 = new Boolean(true)
var true2_ty = typeof(true2)
print(true2_ty)
var true2_val = true2.valueOf()
print(true2_val)

var true3 = Boolean(true) || (new Boolean(true))
var true3_ty = typeof(true3)
print(true3_ty)
var true3_val = true3.valueOf()
print(true3_val)
true3

