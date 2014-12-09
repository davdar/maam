x = String("q")
t = typeof(x)
print(t)
print(x)
print(x.length)

x = new String("q")
t = typeof(x)
print(t)
print(x.length)

x = new String()
print(x.length)


x = "x"
print(x)
x = "x".toString()
print(x)
x = "x".valueOf()
print(x)


x = "abc".charAt()
t = typeof(x)
print(t)
print(x)

x = "abc".charAt(1)
print(x)

x = "abc".charAt(100) + "done"
print(x)

// commenting this out because the following functions 
// are not implemented in concrete init state

// x = "abc".charCodeAt()
// t = typeof(x)
// print(t)
// print(x)

// x = "abc".charCodeAt(100)
// print(x)

// x = String.fromCharCode()
// t = typeof(x)
// print(t)
// print(x)

// x = String.fromCharCode("abc".charCodeAt())
// print(x)


x = ""
print(x.length)
x = "abc"
print(x.length)
