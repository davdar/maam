var false1 = Boolean(false)
var false1_ty = typeof(false1)
print(false1_ty)
var false1_val = false1.valueOf()
print(false1_val)

var false2 = new Boolean(false)
var false2_ty = typeof(false2)
print(false2_ty)
var false2_val = false2.valueOf()
print(false2_val)

var false3 = (Boolean(false) || (new Boolean(false))).toString()
var false3_ty = typeof(false3)
print(false3_ty)
var false3_val = false3.valueOf()
print(false3_val)


