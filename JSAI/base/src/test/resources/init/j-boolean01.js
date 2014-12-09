x = Boolean()
t = typeof(x)
print(t)
print(x)

x = new Boolean()
t = typeof(x)
print(t)
v = x.valueOf()
print(v)
s = x.toString()
print(s)

x = Boolean(true)
print(x)

x = Boolean(false)
print(x)

x = Boolean("")
print(x)

x = Boolean("x")
print(x)

x = Boolean(0)
print(x)

x = Boolean(1)
print(x)

x = Boolean(NaN)
print(x)

x = Boolean(Infinity)
print(x)

x = Boolean(null)
print(x)

x = Boolean(undefined)
print(x)
